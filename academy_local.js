// Moon Base Academy in the browser: harness/lunardig/academy.py ported to JavaScript, running the real engine compiled
// to WebAssembly (bindings/wasm.cpp, built by tools/build_academy_web.sh). With this file and the engine loaded, the
// page needs no server, so the Academy can be hosted as static files (for example on GitHub Pages).
//
// Keep it in step with academy.py: ui/e2e/academy_web.js plays the same scripted games in both and compares every turn.
// Integer arithmetic follows Python's: floor division (fdiv), round-half-to-even (pyRound), and the same tiny bot
// random generator (Rng, mulberry32).
(function (root) {
  "use strict";

  // engine enums (core/include/ld/types.hpp, ledger.hpp, production.hpp)
  const CMD = {OpenAccount: 1, Grant: 2, PlaceOrder: 3, BuySurvey: 5, StakeClaim: 6, Build: 7, Extract: 8, Process: 9,
               SetDemand: 10, Run: 29, SetCustomer: 32};
  const ACTOR = {Human: 0, Bot: 1, Admin: 3};
  const EV = {Trade: 3, Extract: 9, ExtractFail: 10, Process: 11, Upkeep: 32};
  const SELL = 1, PRICE_UPPER = 2, CASH = 0xFFFF;
  const ICE = 0, WATER = 1, LH2 = 2, LOX = 3, REGOLITH = 4;
  const GOOD = {ICE: 0, WATER: 1, LH2: 2, LOX: 3};
  const GOOD_NAME = ["ICE", "WATER", "LH2", "LOX"];
  const PLAYER = 1;

  const fdiv = (a, b) => Math.floor(a / b);   // Python // on exact integers (all values here are far below 2^53)
  function pyRound(x) {                        // Python round(): halves go to the even neighbour
    const f = Math.floor(x), d = x - f;
    return d > 0.5 ? f + 1 : d < 0.5 ? f : (f % 2 === 0 ? f : f + 1);
  }
  const sum = xs => xs.reduce((a, b) => a + b, 0);
  function maxBy(xs, key) {                    // Python max(xs, key=...): the first of equal maxima
    let best, bk, first = true;
    for (const x of xs) {
      const k = key(x);
      if (first || cmp(k, bk) > 0) { best = x; bk = k; first = false; }
    }
    return best;
  }
  function cmp(a, b) {                         // compares numbers, or arrays of numbers like Python tuples
    if (Array.isArray(a)) {
      for (let i = 0; i < Math.min(a.length, b.length); i++) { const c = cmp(a[i], b[i]); if (c) return c; }
      return a.length - b.length;
    }
    return a < b ? -1 : a > b ? 1 : 0;
  }
  const toInt = v => { const n = Math.trunc(Number(v) || 0); return Number.isFinite(n) ? n : 0; };

  class AcademyError extends Error {}

  class Rng {                                  // mulberry32, as academy.Rng
    constructor(seed) { this.s = seed >>> 0; }
    next32() {
      this.s = (this.s + 0x6D2B79F5) >>> 0;
      const s = this.s;
      let t = Math.imul(s ^ (s >>> 15), s | 1) >>> 0;
      t = ((((t + (Math.imul(t ^ (t >>> 7), t | 61) >>> 0)) >>> 0) ^ t) >>> 0);
      return (t ^ (t >>> 14)) >>> 0;
    }
    random() { return this.next32() / 4294967296; }
    randint(a, b) { return a + this.next32() % (b - a + 1); }
    sample(xs, k) {
      xs = xs.slice();
      for (let i = 0; i < k; i++) {
        const j = i + this.next32() % (xs.length - i);
        [xs[i], xs[j]] = [xs[j], xs[i]];
      }
      return xs.slice(0, k);
    }
  }

  // ---------------------------------------------------------------- the module: engine + data
  function createAcademy(Module, data, parcelMeta, parcelRaw) {
    const {levels: LEVELS, shop: SHOP, micro: U, pack: PACK, fuel: FUEL, scan_tier: SCAN_TIER} = data;
    const FUEL_CLASS = FUEL.cls, FUEL_RECIPE = FUEL.recipe, FUEL_WATER = FUEL.water, FUEL_POWER = FUEL.power;
    const packCost = k => SHOP[k].pack * SHOP[k].unit_cost;
    const rows = new Map(parcelMeta.parcels.map(p => [p.id, p]));
    const ids = new Map(parcelMeta.parcels.map(p => [p.name, p.id]));
    let tableHash = null;
    const registerTable = () => {
      if (tableHash === null) tableHash = Module.register_parcel_table(parcelRaw);
      if (tableHash !== parcelMeta.table_sha256) throw new AcademyError("the parcel table does not match its JSON");
      return tableHash;
    };

    function academyRuleset() {
      return {
        goods: [["ICE", 10], ["WATER", 9], ["LH2", 1], ["LOX", 8], ["REGOLITH", 1]].map(([name, mass]) =>
          ({name, mass, claim_yield: name === "ICE" || name === "REGOLITH"})),
        facilities: [{name: "Fuel maker", unit_cost: SHOP.fuel.unit_cost * U, standby_power: 0}],
        recipes: [{name: "Electrolysis", inputs: [[WATER, FUEL_WATER]], outputs: [[LH2, FUEL_WATER], [LOX, FUEL_WATER]],
                   facility: FUEL_CLASS, fac_units: 1, power: FUEL_POWER, duration: 1}],
        cryo_class: 0, ruleset_name: "academy-0.1",
      };
    }

    class Seat {
      constructor(account, name, actor, policy = null, home = null, rng = null) {
        Object.assign(this, {account, name, actor, policy, home, rng});
        this.pending = [];
        this.sales = 0;
        this.sold = {ICE: 0, WATER: 0, LH2: 0, LOX: 0};
        this.dug_turn_max = 0;
        this.jams = 0;
        this.log = [];
        this.bases = [];
        this.lh2Seen = 0;
      }
    }

    class AcademyGame {
      constructor(level = 1, seed = 1) {
        if (!(level >= 1 && level <= LEVELS.length)) throw new AcademyError("no such level");
        this.L = LEVELS[level - 1];
        this.seed = seed;
        this.parcels = "world" in this.L;
        this.me = new Seat(PLAYER, "You", ACTOR.Human, null, (this.L.world || {}).home || null);
        this.bots = (this.L.bots || []).map((b, i) => new Seat(10 + i, b.name, ACTOR.Bot, b.policy, b.home || null, new Rng(seed * 1000 + i)));
        this.keys = new Map();
        this.adminKey = 0;
        if (this.parcels) this._setupParcels(); else this._setupCatalog();
        this.pc = this.e.prod();
        this.turn = 0;
        this.done = this.failed = false;
        this.reason = null;
        this.stars = 0;
        this.market = {};
        this.cursor = this.e.event_count();
      }
      dispose() { if (this.e) { this.e.delete(); this.e = null; } }

      // ---------------- engine plumbing (as lunardig.world.World)
      _key(account) { const k = (this.keys.get(account) || 0) + 1; this.keys.set(account, k); return k; }
      _cmd(seat, type, kw = {}) {
        this.e.submit(Object.assign({type, actor: seat.actor, account: seat.account, key: this._key(seat.account), firm: 0}, kw));
      }
      _admin(type, account, kw = {}) {
        this.adminKey += 1;
        this.e.submit(Object.assign({type, actor: ACTOR.Admin, account, key: this.adminKey}, kw));
      }
      _openAccount(account, actor) { this._admin(CMD.OpenAccount, account, {aux: actor}); }
      _grant(account, good, qty) { this._admin(CMD.Grant, account, {good, qty}); }
      _setDemand(good, pmax, qmax, pmin) { this._admin(CMD.SetDemand, 0, {good, price: pmax, qty: qmax, aux: pmin}); }
      _setCustomer(cid, good, pmax, qmax, pmin, period, phase) {
        this._admin(CMD.SetCustomer, cid, {good, price: pmax, qty: qmax, aux: pmin, aux2: period * 4294967296 + phase});
      }

      _prod(risk) {
        return {public_noise_bps: 0, min_stake: 0, min_work: 0, work_period: 1000,
                unit_cost: ["power", "rig", "plant"].map(k => SHOP[k].unit_cost * U), build_delay: 1,
                base_fail_bps: 0, fail_slope_bps: risk.fail_slope_bps || 0,
                repair_cost: (risk.repair_cost || 0) * U, repair_cycles: risk.repair_cycles || 2,
                upkeep_bps: risk.upkeep_bps || 0, claim_holding_cost: 0, power_per_ore: 1, power_per_ice: 2,
                process_yield_bps: 9000, depletion_grade_decay_bps: 0};
      }
      _setupCatalog() {
        const L = this.L;
        const prod = Object.assign(this._prod(L.risk || {}), {n_deposits: 1, max_claims: 1,
          catalog: [{good: ICE, lat_ude: data.shackleton_ude[0], lon_ude: data.shackleton_ude[1], est_reserve: 1000000, est_grade_bps: 2500}]});
        const e = this.e = new Module.Engine({world_seed: this.seed, num_goods: 2, prod, fin: {demurrage_bps: 0}});
        const s = L.start;
        const setupCost = sum(["power", "rig", "plant"].map(k => s[k] * SHOP[k].unit_cost)) * U;
        this._openAccount(PLAYER, ACTOR.Human);
        this._grant(PLAYER, CASH, s.cash * U + setupCost);
        for (const [name, p] of Object.entries(L.prices)) this._setDemand(GOOD[name], p * U, 1000000, p * U);
        e.advance();
        this._cmd(this.me, CMD.StakeClaim, {aux: 0, price: 0});
        for (const k of ["power", "rig", "plant"]) if (s[k]) this._cmd(this.me, CMD.Build, {aux: SHOP[k].kind, qty: s[k]});
        e.advance();
        e.advance();
        const short = s.cash * U - this._acc().cash_free;
        if (short) {
          const pc = e.prod(), a = this._acc();
          const due = sum([a.power_cap, a.rig_cap, a.plant_cap].map((cap, i) => fdiv(cap * pc.unit_cost[i] * pc.upkeep_bps, 10000)));
          this._grant(PLAYER, CASH, short + due);
          e.advance();
        }
        this.me.bases = [0];
        this.start_cycle = e.cycle();
      }
      _setupParcels() {
        const L = this.L, W = L.world;
        const prod = Object.assign(this._prod({}), {n_deposits: 0, parcel_mode: true, parcel_table: registerTable(), auction_cycles: 3,
          reserved_parcels: [], max_claims: W.max_claims, public_noise_bps: W.noise_bps,
          ice_grade_scale_bps: data.ice_grade_scale, ice_per_km2: W.ice_per_km2,
          survey_cost: [0, 0, 0].map(() => (L.scan_cost || 10) * U), survey_noise_bps: [2500, 1200, 300],
          ilmenite_good: REGOLITH, iron_good: REGOLITH, fines_good: REGOLITH, mare_fines_good: REGOLITH,
          earth_levels: L.market ? 11 : 8});
        const e = this.e = new Module.Engine({world_seed: this.seed, content: academyRuleset(), prod, fin: {demurrage_bps: 0}, price_rule: PRICE_UPPER});
        const s = L.start;
        this.map = W.map.map(n => ids.get(n));
        for (const x of this.bots) if (x.home && !W.map.includes(x.home)) throw new AcademyError("a bot's home must be on the map");
        const setupCost = sum(Object.keys(SHOP).map(k => (s[k] || 0) * SHOP[k].unit_cost)) * U;
        for (const seat of this.seats()) {
          this._openAccount(seat.account, seat.actor);
          this._grant(seat.account, CASH, s.cash * U + setupCost);
        }
        const market = L.market || {};
        for (const [name, p] of Object.entries(L.prices)) {
          if (name in market) { const [hi, lo, q] = market[name]; this._setDemand(GOOD[name], hi * U, q, lo * U); }
          else this._setDemand(GOOD[name], p * U, 1000000, p * U);
        }
        e.advance();
        for (const seat of this.seats()) {
          if (seat.home) this._cmd(seat, CMD.StakeClaim, {aux: ids.get(seat.home), price: 0});
          for (const k of Object.keys(SHOP)) if (s[k]) this._cmd(seat, CMD.Build, {aux: SHOP[k].kind, qty: s[k]});
        }
        for (let i = 0; i < e.prod().auction_cycles; i++) e.advance();
        for (const seat of this.seats()) if (seat.home) seat.bases = [ids.get(seat.home)];
        const R = L.rocket;
        if (R) {
          const phase = e.cycle() + 1 + R.first - 1;
          Object.entries(R.buys).forEach(([name, [p, q]], i) => this._setCustomer(20 + i, GOOD[name], p * U, q, p * U, R.every, phase));
        }
        e.advance();
        this.start_cycle = e.cycle();
      }
      seats() { return [this.me, ...this.bots]; }

      _acc(seat) { return this.e.account((seat || this.me).account); }
      cash(seat) { return fdiv(this._acc(seat).cash_free, U); }
      stock(good, seat) { return this.e.balance((seat || this.me).account, good); }
      hasFuel() { return this.L.shop.includes("fuel"); }
      machines(seat) {
        seat = seat || this.me;
        const a = this._acc(seat), cycle = this.e.cycle();
        const m = {power: a.power_cap, rig: a.rig_cap, plant: a.plant_cap};
        if (this.hasFuel()) m.fuel = this.e.facility_units(seat.account, FUEL_CLASS);
        for (const [ready, k, units] of seat.pending) if (ready <= cycle && k in m) m[k] += units;
        return m;
      }
      fuelBusy(seat) {
        seat = seat || this.me;
        if (!this.hasFuel()) return [0, 0];
        const cycle = this.e.cycle();
        const runs = sum(this.e.jobs().filter(j => j.account === seat.account && j.finish >= cycle).map(j => j.runs));
        return [runs, runs * FUEL_POWER];
      }
      upkeepDue(m) {
        m = m || this.machines();
        return fdiv(sum(Object.keys(m).map(k => m[k] * SHOP[k].unit_cost)) * this.pc.upkeep_bps, 10000);
      }
      jamBps(dig, seat) {
        const rig = this.machines(seat).rig;
        if (dig <= 0 || rig <= 0) return 0;
        const util = fdiv(dig * 10000, rig);
        return Math.min(10000, this.pc.base_fail_bps + fdiv(this.pc.fail_slope_bps * util * util, 1e8));
      }

      // ---------------- parcels
      _dep(pid) {
        const d = this.parcels ? this.e.deposit_of_parcel(pid) : pid;
        return d === null || d < 0 ? null : this.e.deposits()[d];
      }
      iceLeft(base) { const d = this._dep(base); return d ? d.remaining : 0; }
      _stakes(seat) {
        const out = new Map(), deps = this.e.deposits();
        for (const a of this.e.auctions()) for (const st of a.stakes) if (st.who === seat.account) out.set(deps[a.deposit].parcel, fdiv(st.bid, U));
        return out;
      }
      _scans(seat) {
        const out = new Map(), deps = this.e.deposits();
        for (const s of this.e.surveys(seat.account)) out.set(deps[s.deposit].parcel, [s.est_grade_bps, s.est_reserve]);
        return out;
      }
      _public(pid) {
        const f = rows.get(pid), pc = this.pc;
        const shadow = fdiv(f.area * f.psr, 10000);
        return [Math.min(10000, fdiv(f.ice * pc.ice_grade_scale_bps, 10000)), fdiv(shadow * pc.ice_per_km2, 1000)];
      }
      _owner(pid) {
        const d = this._dep(pid);
        if (!d || d.owner === null) return null;
        return this.seats().find(s => s.account === d.owner) || null;
      }
      _parse(name) {
        const pid = typeof name === "string" ? ids.get(name) : undefined;
        return pid !== undefined && this.map.includes(pid) ? pid : null;
      }
      _name(pid) { return this.parcels ? rows.get(pid).name : "your parcel"; }

      // ---------------- planning
      preview(plan, seat) {
        seat = seat || this.me;
        plan = plan || {};
        const m = this.machines(seat), a = this._acc(seat);
        const cash = fdiv(a.cash_free, U);
        const down = this.e.cycle() < a.rig_down_until;
        let melt = Math.max(0, toInt(plan.melt));
        let runs = this.hasFuel() ? Math.max(0, toInt(plan.fuel)) : 0;
        let sell = (plan.sell || []).filter(g => this._sellable().includes(g));
        let buy = {};
        for (const [k, v] of Object.entries(plan.buy || {})) if (this.L.shop.includes(k)) buy[k] = Math.max(0, toInt(v));
        const problems = [];
        const ice = this.stock(ICE, seat), water = this.stock(WATER, seat);

        const raw = plan.dig || 0;
        const bases = seat.bases.slice();
        let want = new Map();
        const isDict = typeof raw === "object" && raw !== null;
        if (isDict) {
          for (const [k, v] of Object.entries(raw)) {
            const pid = ids.get(k);
            if (pid === undefined) continue;
            if (bases.includes(pid)) want.set(pid, (want.get(pid) || 0) + Math.max(0, toInt(v)));
          }
        } else {
          let left = Math.max(0, toInt(raw));
          for (const b of bases) {
            const take = this.parcels && b !== bases[bases.length - 1] ? Math.min(left, this.iceLeft(b)) : left;
            if (take) want.set(b, take);
            left -= take;
          }
        }
        if (!bases.length && sum([...want.values()]) === 0 && (isDict ? 0 : toInt(raw)))
          problems.push("You have no parcel to dig yet. Win one on the map first.");
        if (sum([...want.values()]) > m.rig) {
          problems.push(`You only have drills for ${m.rig} loads.`);
          want = cut(want, sum([...want.values()]) - m.rig);
        }
        let digAt = new Map();
        for (const b of bases) {
          let n = want.get(b) || 0;
          if (this.parcels && n > this.iceLeft(b)) {
            problems.push(`${this._name(b)} has only ${this.iceLeft(b)} loads of ice left.`);
            n = this.iceLeft(b);
          }
          if (n) digAt.set(b, n);
        }
        let dig = sum([...digAt.values()]);
        if (down && dig) {
          problems.push(`The drills are being repaired until turn ${a.rig_down_until - this.start_cycle + 1}: no digging.`);
          digAt = new Map(); dig = 0;
        }
        if (dig > m.rig) {
          problems.push(`You only have drills for ${m.rig} loads.`);
          digAt = cut(digAt, dig - m.rig);
          dig = m.rig;
        }
        if (melt > m.plant) {
          problems.push(`Your melters can only melt ${m.plant} ice a turn.`);
          melt = m.plant;
        }
        const sellIce = sell.includes("ICE");
        if (melt > ice || (sellIce && melt)) {
          if (sellIce && melt) { problems.push("You can't melt ice and sell it in the same turn: choose one."); melt = 0; }
          else { problems.push(`You only have ${ice} ice to melt.`); melt = ice; }
        }
        const [busyRuns, busyPower] = this.fuelBusy(seat);
        if (runs) {
          const free = (m.fuel || 0) - busyRuns;
          if (free < runs) {
            problems.push((m.fuel || 0) === 0 ? "Buy a fuel maker first: it starts working next turn." :
              `Your fuel makers can start ${Math.max(0, free)} job${free !== 1 ? "s" : ""} this turn (a job takes 2 turns).`);
            runs = Math.max(0, free);
          }
          if (runs * FUEL_WATER > water) {
            problems.push(`Each fuel job needs ${FUEL_WATER} water: you have ${water}.`);
            runs = fdiv(water, FUEL_WATER);
          }
        }
        let power = busyPower + dig + 2 * melt + FUEL_POWER * runs;
        if (power > m.power) {
          problems.push(`Not enough power: that needs ${power}, you have ${m.power}.`);
          let over = power - m.power;
          let c = Math.min(runs, fdiv(over + FUEL_POWER - 1, FUEL_POWER));
          runs -= c;
          over = Math.max(0, over - c * FUEL_POWER);
          c = Math.min(melt, fdiv(over + 1, 2));
          melt -= c;
          over = Math.max(0, over - 2 * c);
          if (over) { digAt = cut(digAt, over); dig = sum([...digAt.values()]); }
          power = busyPower + dig + 2 * melt + FUEL_POWER * runs;
        }

        const scans = [], bids = new Map();
        if (this.parcels) {
          const known = this._scans(seat);
          for (const name of plan.scan || []) {
            const pid = this._parse(name);
            if (pid === null || scans.includes(pid)) continue;
            if (known.has(pid)) { problems.push(`You already scanned ${this._name(pid)}.`); continue; }
            if (this._owner(pid) !== null) continue;
            scans.push(pid);
          }
          const openStakes = this._stakes(seat);
          let room = this.pc.max_claims - seat.bases.length - openStakes.size;
          for (const [name, v] of Object.entries(plan.bid || {})) {
            const pid = this._parse(name), amount = Math.max(0, toInt(v));
            if (pid === null || !amount) continue;
            if (this._owner(pid) !== null) problems.push(`${this._name(pid)} already belongs to ${this._owner(pid).name}.`);
            else if (openStakes.has(pid)) problems.push(`You already bid ${openStakes.get(pid)} on ${this._name(pid)}: wait for the auction to end.`);
            else if (room <= 0) problems.push(!seat.bases.length || this.pc.max_claims > 1 ? "You can only bid for one parcel at a time." : "You already have a parcel.");
            else { bids.set(pid, amount); room -= 1; }
          }
        }
        const scanEach = this.L.scan_cost || 10;
        let scanCost = scans.length * scanEach;
        while (scans.length && scanCost > cash) { scans.pop(); scanCost -= scanEach; }
        for (const pid of [...bids.keys()]) {
          if (scanCost + sum([...bids.values()]) > cash) { problems.push(`You have ${cash} credits: not enough for that bid.`); bids.delete(pid); }
        }
        const spare = cash - scanCost - sum([...bids.values()]);

        let cost = sum(Object.entries(buy).map(([k, n]) => n * packCost(k)));
        let earn = 0;
        if (!this.rocketHere()) sell = sell.filter(g => g !== "LH2" && g !== "LOX");
        for (const g of sell) {
          const have = this.stock(GOOD[g], seat) - (g === "WATER" ? FUEL_WATER * runs : 0);
          earn += Math.max(0, have) * this._price(g, 0);
        }
        if (cost > spare) {
          problems.push(`You have ${spare} credits: not enough for all that. Sell first, buy more next turn.`);
          const last = plan.last;
          while (cost > spare) {
            const k = buy[last] ? last : maxBy(Object.keys(buy).filter(k => buy[k]), k => packCost(k));
            buy[k] -= 1;
            cost -= packCost(k);
          }
          const kept = {};
          for (const [k, n] of Object.entries(buy)) if (n) kept[k] = n;
          buy = kept;
        }
        const warn = [];
        if (this.pc.upkeep_bps && cost) {
          const after = Object.assign({}, m);
          for (const [k, n] of Object.entries(buy)) after[k] += n * SHOP[k].pack;
          const left = cash - cost + earn;
          const need = this.upkeepDue(after) + fdiv(this.pc.repair_cost, U);
          if (left < need)
            warn.push(`Careful: after buying you will have about ${left} credits. Upkeep is ${this.upkeepDue(after)} a turn ` +
                      `and a repair costs ${fdiv(this.pc.repair_cost, U)}. Run out and the drills stop.`);
        }
        const iceNext = this.parcels ? sum([...digAt.entries()].map(([b, n]) => fdiv(n * this._dep(b).grade_bps, 10000)))
                                     : fdiv(dig * this.e.deposits()[0].grade_bps, 10000);
        const digAtNames = {};
        for (const [b, n] of digAt) digAtNames[this._name(b)] = n;
        const bidNames = {};
        for (const [p, v] of bids) bidNames[this._name(p)] = v;
        return {warnings: warn, dig, dig_at: digAtNames, melt, fuel: runs, sell, buy, scan: scans.map(p => this._name(p)), bid: bidNames,
                power_used: power, power_busy: busyPower, power: m.power,
                ice_next: iceNext, water_next: fdiv(melt * this.pc.process_yield_bps, 10000),
                fuel_next: runs * FUEL_WATER, earn, cost: cost + scanCost + sum([...bids.values()]),
                jam_bps: this.jamBps(dig, seat), problems, rigs_down: down};
      }
      _sellable() {
        const goods = Object.keys(this.L.prices);
        if (this.L.rocket) goods.push(...Object.keys(this.L.rocket.buys));
        return goods;
      }
      _price(good, which = 1) {
        const R = this.L.rocket;
        if (R && good in R.buys) return R.buys[good][0];
        if (good in (this.L.market || {})) {
          const last = this.market[good];
          return last && last.price && which === 0 ? last.price : this.L.market[good][0];
        }
        return this.L.prices[good];
      }
      _ask(good) { return good in (this.L.market || {}) ? this.L.market[good][1] : this._price(good); }
      rocketHere(turn) {
        const R = this.L.rocket, t = turn === undefined ? this.turn + 1 : turn;
        return !!R && t >= R.first && (t - R.first) % R.every === 0;
      }
      rocketNext() { let t = this.turn + 1; while (!this.rocketHere(t)) t += 1; return t; }

      // ---------------- bots
      botPlan(seat) {
        let m = this.machines(seat);
        const cash = this.cash(seat);
        const plan = {dig: 0, melt: 0, sell: [], buy: {}, scan: [], bid: {}};
        if (seat.policy === "prospector" && !seat.bases.length) {
          if (this._stakes(seat).size) return plan;
          const known = this._scans(seat);
          const free = this.map.filter(p => this._owner(p) === null && !known.has(p));
          if (!known.size && free.length && this.L.scan_cost) {
            plan.scan = seat.rng.sample(free, Math.min(2, free.length)).map(p => this._name(p));
            return plan;
          }
          const open = this.map.filter(p => this._owner(p) === null);
          if (open.length) {
            const best = maxBy(open, p => [(known.get(p) || this._public(p))[0], seat.rng.random()]);
            plan.bid = {[this._name(best)]: Math.min(fdiv(cash, 3), 10 * seat.rng.randint(3, 8))};
          }
          return plan;
        }
        if (seat.policy === "prospector" && this.pc.max_claims > seat.bases.length &&
            sum(seat.bases.map(b => this.iceLeft(b))) < 4 * m.rig && !this._stakes(seat).size) {
          const open = this.map.filter(p => this._owner(p) === null);
          if (open.length) plan.bid = {[this._name(maxBy(open, p => this._public(p)[1]))]: Math.min(fdiv(cash, 3), 40)};
        }
        const ice = this.stock(ICE, seat);
        const water = "WATER" in this.L.prices && m.plant > 0;
        const melt = water ? Math.min(ice, m.plant, fdiv(m.power, 2)) : 0;
        Object.assign(plan, {melt, dig: Math.max(0, Math.min(m.rig, m.power - 2 * melt)), sell: water ? ["WATER"] : ["ICE"]});
        if (water && ice && !melt) plan.sell = ["ICE", "WATER"];
        let spare = cash - 60;
        for (let i = 0; i < 3; i++) {
          const need = {power: m.rig * 1.5 - m.power, rig: m.rig < 80 ? 10 : -1, plant: water ? m.rig * 0.25 - m.plant : -1};
          const k = maxBy(Object.keys(need), k => need[k]);
          if (need[k] <= 0 || spare < packCost(k)) break;
          plan.buy[k] = (plan.buy[k] || 0) + 1;
          spare -= packCost(k);
          m = Object.assign({}, m);
          m[k] += PACK;
        }
        return plan;
      }

      // ---------------- the turn
      _submit(seat, plan) {
        const p = this.preview(plan, seat);
        const digs = this.parcels ? Object.entries(p.dig_at).map(([k, n]) => [this._parse(k), n]) : (p.dig ? [[0, p.dig]] : []);
        for (const [b, n] of digs) this._cmd(seat, CMD.Extract, {aux: b, qty: n});
        if (p.melt) this._cmd(seat, CMD.Process, {qty: p.melt});
        if (p.fuel) this._cmd(seat, CMD.Run, {aux: FUEL_RECIPE, qty: p.fuel});
        for (const g of p.sell) {
          const qty = this.stock(GOOD[g], seat);
          if (qty > 0) this._cmd(seat, CMD.PlaceOrder, {good: GOOD[g], side: SELL, price: this._ask(g) * U, qty});
        }
        for (const [k, n] of Object.entries(p.buy)) {
          if (n) {
            this._cmd(seat, CMD.Build, {aux: SHOP[k].kind, qty: n * SHOP[k].pack});
            seat.pending.push([this.e.cycle() + this.pc.build_delay, k, n * SHOP[k].pack]);
          }
        }
        for (const name of p.scan) this._cmd(seat, CMD.BuySurvey, {aux: this._parse(name), qty: SCAN_TIER});
        for (const [name, v] of Object.entries(p.bid)) this._cmd(seat, CMD.StakeClaim, {aux: this._parse(name), price: v * U});
        return p;
      }
      endTurn(plan) {
        if (this.done || this.failed) throw new AcademyError("this level is over: start it again or pick another");
        const had = new Map(this.seats().map(s => [s.account, s.bases.slice()]));
        const botPlans = this.bots.map(s => [s, this.botPlan(s)]);
        const stakesBefore = this.parcels ? new Map(this.seats().map(s => [s.account, this._stakes(s)])) : new Map();
        const rocket = this.rocketHere();
        const plans = [[this.me, this._submit(this.me, plan || {})], ...botPlans.map(([s, bp]) => [s, this._submit(s, bp)])];
        this.e.advance();
        const cycle = this.e.cycle();
        for (const s of this.seats()) s.pending = s.pending.filter(x => x[0] >= cycle);
        this.turn += 1;
        const ev = this.e.events_since(this.cursor);
        this.cursor = this.e.event_count();
        const rec = new Map(this.seats().map(s => [s.account, {got: {ICE: 0, WATER: 0, LH2: 0, LOX: 0}, sold: {ICE: 0, WATER: 0, LH2: 0, LOX: 0},
                                                                earned: 0, dug: 0, jam: false, upkeep: 0, repair: 0}]));
        const market = {};
        for (const [t, , who, good, a, b, cc] of ev) {
          const r = rec.get(who);
          if (!r) continue;
          if (t === EV.Extract) { r.dug += a; r.got.ICE += cc; }
          else if (t === EV.ExtractFail) { r.jam = true; r.repair += fdiv(b, U); }
          else if (t === EV.Process) r.got.WATER += b;
          else if (t === EV.Trade && a < 0 && good < GOOD_NAME.length) {
            const name = GOOD_NAME[good];
            r.sold[name] += -a;
            r.earned += fdiv(cc, U);
            const mk = market[name] || (market[name] = {sold: 0, earned: 0});
            mk.sold += -a;
            mk.earned += fdiv(cc, U);
          } else if (t === EV.Upkeep) r.upkeep += fdiv(a, U);
        }
        for (const mk of Object.values(market)) mk.price = mk.sold ? fdiv(mk.earned, mk.sold) : 0;
        for (const name of Object.keys(this.L.market || {})) this.market[name] = market[name] || {sold: 0, earned: 0, price: this.L.market[name][0]};
        const events = this.parcels ? this._claimsUpdate(stakesBefore) : new Map();
        for (const [s, p] of plans) {
          const r = rec.get(s.account);
          s.sales += r.earned;
          for (const g of Object.keys(r.sold)) s.sold[g] += r.sold[g];
          s.dug_turn_max = Math.max(s.dug_turn_max, r.dug);
          s.jams += r.jam ? 1 : 0;
          const bought = {};
          for (const [k, n] of Object.entries(p.buy)) if (n) bought[k] = n;
          const entry = {turn: this.turn, down: !!p.rigs_down, dug: r.dug, got: r.got, sold: r.sold, earned: r.earned,
                         jam: r.jam, repair: r.repair, upkeep: r.upkeep, bought, problems: p.problems};
          if (this.parcels) Object.assign(entry, {had_base: had.get(s.account).length > 0, scanned: p.scan, bid: p.bid,
                                                   claims: events.get(s.account) || [], fuel: p.fuel, rocket});
          if (this.hasFuel()) entry.fuel_ready = this._fuelReady(s);
          s.log.push(entry);
        }
        this.reason = null;
        this._checkGoal();
        return this.state();
      }
      _fuelReady(seat) {
        const now = this.stock(LH2, seat) + seat.sold.LH2;
        const out = Math.max(0, now - seat.lh2Seen);
        seat.lh2Seen = now;
        return out;
      }
      _claimsUpdate(stakesBefore) {
        const out = new Map();
        for (const s of this.seats()) {
          for (const [pid, amount] of (stakesBefore.get(s.account) || new Map())) {
            if (this._stakes(s).has(pid)) continue;
            const owner = this._owner(pid);
            if (!out.has(s.account)) out.set(s.account, []);
            if (owner === s) {
              s.bases.push(pid);
              out.get(s.account).push(`won ${this._name(pid)} for ${amount} credits`);
            } else {
              out.get(s.account).push(`lost ${this._name(pid)} to ${owner ? owner.name : "nobody"} (your ${amount} credits came back)`);
            }
          }
        }
        return out;
      }

      // ---------------- goals
      progress() {
        const g = this.L.goal, k = g.kind, s = this.me;
        const now = k === "sales" ? s.sales : k === "dig_turn" ? s.dug_turn_max : k === "sold" ? s.sold[g.good] :
          k === "sold_fuel" ? s.sold.LH2 + s.sold.LOX : fdiv(this._acc().cash_free, U);
        return [Math.min(now, g.target), g.target];
      }
      _checkGoal() {
        const [now, target] = this.progress();
        if (now >= target) {
          this.done = true;
          const [three, two] = this.L.stars;
          this.stars = this.turn <= three ? 3 : this.turn <= two ? 2 : 1;
          if (this.L.star_rule === "no_jams" && this.me.jams && this.stars === 3) this.stars = 2;
        } else if (this.turn >= this.L.turns) {
          this.failed = true;
          this.reason = "turns";
        } else if (this.pc.upkeep_bps && fdiv(this._acc().cash_free, U) < this.upkeepDue() && !this.stock(ICE) && !this.stock(WATER)) {
          this.failed = true;
          this.reason = "broke";
        } else if (this.parcels && !this.me.bases.length && !this._stakes(this.me).size && this.map.every(p => this._owner(p) !== null)) {
          this.failed = true;
          this.reason = "no_parcel";
        }
      }
      hint() {
        const m = this.machines(), a = this._acc();
        const ice = this.stock(ICE), water = this.stock(WATER), cash = fdiv(a.cash_free, U);
        const L = this.L, log = this.me.log;
        if (this.reason === "broke") return "Keep some credits for upkeep and repairs: buy machines a few at a time, and dig at about 70%.";
        if (this.reason === "no_parcel") return "Every parcel was taken. Next time bid early, and bid a little more.";
        if (this.failed) return L.fail_hint;
        if (this.parcels && !this.me.bases.length) {
          if (this._stakes(this.me).size) return "Your bid is in. The auction ends in a few turns: the highest bid wins.";
          if (!this._scans(this.me).size && L.scan_cost) return "Tap a parcel on the map and press Scan to see how much ice it really has.";
          return "Pick a parcel on the map and bid for it. Bids are secret: bid enough to win.";
        }
        if (this.turn === 0) return L.hints[0];
        if (this.parcels && this.me.bases.length < this.pc.max_claims && !this._stakes(this.me).size &&
            sum(this.me.bases.map(b => this.iceLeft(b))) < 4 * Math.max(10, m.rig))
          return "Your parcel is running out of ice. Bid for another parcel on the map now: auctions take 3 turns.";
        if (this.parcels && this.me.bases.length > 1 && log.length && log[log.length - 1].dug < m.rig) {
          const empty = this.me.bases.filter(b => !this.iceLeft(b)), full = this.me.bases.filter(b => this.iceLeft(b));
          if (empty.length && full.length) return `${this._name(empty[0])} is empty. Press + to dig at ${this._name(full[0])} instead.`;
        }
        if (this.hasFuel()) {
          if (this.rocketHere() && (this.stock(LH2) || this.stock(LOX))) return "The rocket is here! Tick Sell hydrogen and Sell oxygen.";
          if (!m.fuel) return "Buy a fuel maker in the shop: it turns water into rocket fuel.";
          if (water >= FUEL_WATER && this.fuelBusy()[0] < m.fuel) return `You have water: press + next to Make fuel. The rocket lands on turn ${this.rocketNext()}.`;
        }
        const lastE = log[log.length - 1];
        if (m.rig && this.me.bases.length && (lastE.had_base === undefined ? true : lastE.had_base) && !lastE.dug && !lastE.jam && this.e.cycle() >= a.rig_down_until)
          return "Your drills did nothing last turn. Press + next to Dig.";
        if (L.market && this.market.WATER) {
          const p = this.market.WATER.price;
          if (p && 9 * p < 10 * L.prices.ICE) return `Water sold for only ${p} last turn: 9 water make ${9 * p}, but 10 ice make ${10 * L.prices.ICE}. Sell ice!`;
        }
        if (water && "WATER" in L.prices && !this.hasFuel()) return "You have water in the store: tick Sell water.";
        if (ice && "WATER" in L.prices && m.plant) return "You have ice: melt it into water, which sells for more.";
        if (ice) return "You have ice in the store: tick Sell ice.";
        if (L.shop.length && m.power < m.rig && cash >= packCost("power")) return "Your drills are waiting for power. Buy a solar panel.";
        return L.hints[Math.min(L.hints.length - 1, fdiv(this.turn, 3))];
      }
      mapState() {
        const scans = this._scans(this.me), mine = this._stakes(this.me);
        const bidders = new Map(), deps = this.e.deposits();
        for (const a of this.e.auctions()) bidders.set(deps[a.deposit].parcel, a.closes - this.start_cycle + 2);
        return this.map.map(pid => {
          const info = rows.get(pid);
          const [grade, reserve] = this._public(pid);
          const owner = this._owner(pid);
          const row = {name: info.name, x: info.x, y: info.y, size: info.size, est_pct: pyRound(grade / 100), est_ice: reserve,
                       shadow_pct: info.psr_pct, where: info.where,
                       owner: owner === null ? null : owner === this.me ? "you" : owner.name,
                       auction: bidders.has(pid), result_turn: bidders.has(pid) ? bidders.get(pid) : null,
                       my_bid: mine.has(pid) ? mine.get(pid) : null};
          if (scans.has(pid)) { row.scan_pct = pyRound(scans.get(pid)[0] / 100); row.scan_ice = scans.get(pid)[1]; }
          if (owner === this.me) { const d = this._dep(pid); row.ice_left = d.remaining; row.grade_pct = pyRound(d.grade_bps / 100); }
          return row;
        });
      }
      state() {
        const m = this.machines(), a = this._acc(), L = this.L;
        const [now, target] = this.progress();
        let bases, grade;
        if (this.parcels) {
          bases = this.me.bases.map(b => ({name: this._name(b), grade_pct: pyRound(this._dep(b).grade_bps / 100), ice_left: this.iceLeft(b)}));
          grade = bases.length ? bases[0].grade_pct : 0;
        } else {
          grade = this.e.deposits()[0].grade_bps / 100;
        }
        const prices = {};
        for (const g of this._sellable()) prices[g] = this._price(g);
        const st = {level: L.n, title: L.title, place: L.place, story: L.story, learn: L.learn,
          goal: {text: L.goal.text, now, target}, turn: this.turn, turns: L.turns,
          stars_at: L.stars.slice(), star_rule: L.star_rule === undefined ? null : L.star_rule,
          cash: fdiv(a.cash_free, U), ice: this.stock(ICE), water: this.stock(WATER), machines: m,
          rigs_down_until: this.e.cycle() < a.rig_down_until ? a.rig_down_until - this.start_cycle + 1 : null,
          prices, grade_pct: grade, yield_pct: this.pc.process_yield_bps / 100,
          shop: L.shop.map(k => ({id: k, name: SHOP[k].name, gives: SHOP[k].gives, cost: packCost(k)})),
          risk: {jams: !!L.risk, upkeep_pct: this.pc.upkeep_bps / 100, repair_cost: fdiv(this.pc.repair_cost, U)},
          jams: this.me.jams, sales: this.me.sales, sold: Object.assign({}, this.me.sold),
          upkeep_due: this.upkeepDue(), log: this.me.log.slice(-12), done: this.done, failed: this.failed,
          reason: this.reason, stars: this.stars, hint: this.hint()};
        if (this.parcels) {
          Object.assign(st, {bases, map: this.mapState(), scan_cost: L.scan_cost === undefined ? null : L.scan_cost, max_claims: this.pc.max_claims,
            rivals: this.bots.map(s => ({name: s.name, bases: s.bases.map(b => this._name(b)), sales: s.sales,
                                         last: s.log.length ? {sold: s.log[s.log.length - 1].sold, earned: s.log[s.log.length - 1].earned} : null}))});
        }
        if (L.market) {
          st.market = {};
          for (const [g, v] of Object.entries(L.market)) st.market[g] = {top: v[0], bottom: v[1], last: this.market[g] === undefined ? null : this.market[g]};
        }
        if (this.hasFuel()) {
          const [busy, busyPower] = this.fuelBusy();
          const buys = {};
          for (const [g, [p, q]] of Object.entries(L.rocket.buys)) buys[g] = {price: p, qty: q};
          Object.assign(st, {lh2: this.stock(LH2), lox: this.stock(LOX), fuel_busy: busy, fuel_power: busyPower,
            rocket: {here: this.rocketHere(), next: this.rocketNext(), every: L.rocket.every, buys}});
        }
        return st;
      }
    }

    function cut(digAt, n) {                    // dig n loads fewer, from the last bases first
      const out = new Map(digAt);
      for (const b of [...out.keys()].reverse()) {
        const take = Math.min(out.get(b), n);
        out.set(b, out.get(b) - take);
        n -= take;
        if (!out.get(b)) out.delete(b);
      }
      return out;
    }

    const levelList = () => LEVELS.map(L => ({n: L.n, title: L.title, place: L.place, learn: L.learn, goal: L.goal.text, turns: L.turns}));

    // The same JSON API as ui/academy.py, answered in the page. One game at a time; starting another frees the last.
    let current = null, token = null;
    function call(path, body) {
      if (path === "/api/levels") return {levels: levelList()};
      if (path === "/api/start") {
        const level = toInt((body || {}).level || 1);
        const g = new AcademyGame(level, Math.floor(Math.random() * 1000000) + 1);
        if (current) current.dispose();
        current = g;
        token = Math.random().toString(16).slice(2);
        return {token, state: g.state()};
      }
      if (!current || !body || body.token !== token) throw new AcademyError("that game has ended: start the level again");
      if (path === "/api/preview") return current.preview(body.plan || {});
      if (path === "/api/turn") return current.endTurn(body.plan || {});
      if (path === "/api/state") return current.state();
      throw new AcademyError("not found");
    }
    return {AcademyGame, AcademyError, Rng, levelList, call, LEVELS};
  }

  // In the browser: load the engine and the data next to this file, then answer the page's API calls.
  function boot(base) {
    const get = (f, kind) => fetch(base + f).then(r => { if (!r.ok) throw new Error(f + ": " + r.status); return r[kind](); });
    return Promise.all([root.LunarDigEngine({locateFile: f => base + f}), get("academy_levels.json", "json"),
                        get("academy_parcels.json", "json"), get("academy_parcels.bin", "arrayBuffer")])
      .then(([Module, data, meta, raw]) => createAcademy(Module, data, meta, new Uint8Array(raw)));
  }

  const api = {createAcademy, boot, Rng, AcademyError};
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else root.LocalAcademy = api;
})(typeof window !== "undefined" ? window : globalThis);
