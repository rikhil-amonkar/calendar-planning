import json
from z3 import *

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mn = m % 60
    return f"{h}:{mn:02d}"

def build_travel():
    t = {}
    def add(a,b,mins):
        t[(a,b)] = mins
    add("Bayview","Nob Hill",20)
    add("Bayview","Union Square",17)
    add("Bayview","Chinatown",18)
    add("Bayview","The Castro",20)
    add("Bayview","Presidio",31)
    add("Bayview","Pacific Heights",23)
    add("Bayview","Russian Hill",23)

    add("Nob Hill","Bayview",19)
    add("Nob Hill","Union Square",7)
    add("Nob Hill","Chinatown",6)
    add("Nob Hill","The Castro",17)
    add("Nob Hill","Presidio",17)
    add("Nob Hill","Pacific Heights",8)
    add("Nob Hill","Russian Hill",5)

    add("Union Square","Bayview",15)
    add("Union Square","Nob Hill",9)
    add("Union Square","Chinatown",7)
    add("Union Square","The Castro",19)
    add("Union Square","Presidio",24)
    add("Union Square","Pacific Heights",15)
    add("Union Square","Russian Hill",13)

    add("Chinatown","Bayview",22)
    add("Chinatown","Nob Hill",8)
    add("Chinatown","Union Square",7)
    add("Chinatown","The Castro",22)
    add("Chinatown","Presidio",19)
    add("Chinatown","Pacific Heights",10)
    add("Chinatown","Russian Hill",7)

    add("The Castro","Bayview",19)
    add("The Castro","Nob Hill",16)
    add("The Castro","Union Square",19)
    add("The Castro","Chinatown",20)
    add("The Castro","Presidio",20)
    add("The Castro","Pacific Heights",16)
    add("The Castro","Russian Hill",18)

    add("Presidio","Bayview",31)
    add("Presidio","Nob Hill",18)
    add("Presidio","Union Square",22)
    add("Presidio","Chinatown",21)
    add("Presidio","The Castro",21)
    add("Presidio","Pacific Heights",11)
    add("Presidio","Russian Hill",14)

    add("Pacific Heights","Bayview",22)
    add("Pacific Heights","Nob Hill",8)
    add("Pacific Heights","Union Square",12)
    add("Pacific Heights","Chinatown",11)
    add("Pacific Heights","The Castro",16)
    add("Pacific Heights","Presidio",11)
    add("Pacific Heights","Russian Hill",7)

    add("Russian Hill","Bayview",23)
    add("Russian Hill","Nob Hill",5)
    add("Russian Hill","Union Square",11)
    add("Russian Hill","Chinatown",9)
    add("Russian Hill","The Castro",21)
    add("Russian Hill","Presidio",14)
    add("Russian Hill","Pacific Heights",7)
    return t

def main():
    travel = build_travel()
    start_city = "Bayview"
    arrival_time = time_to_minutes("9:00")

    persons = {
        "Paul":     {"location":"Nob Hill",       "avail_start":time_to_minutes("16:15"), "avail_end":time_to_minutes("21:15"), "min_dur":60},
        "Carol":    {"location":"Union Square",   "avail_start":time_to_minutes("18:00"), "avail_end":time_to_minutes("20:15"), "min_dur":120},
        "Patricia": {"location":"Chinatown",      "avail_start":time_to_minutes("20:00"), "avail_end":time_to_minutes("21:30"), "min_dur":75},
        "Karen":    {"location":"The Castro",     "avail_start":time_to_minutes("17:00"), "avail_end":time_to_minutes("19:00"), "min_dur":45},
        "Nancy":    {"location":"Presidio",       "avail_start":time_to_minutes("11:45"), "avail_end":time_to_minutes("22:00"), "min_dur":30},
        "Jeffrey":  {"location":"Pacific Heights","avail_start":time_to_minutes("20:00"), "avail_end":time_to_minutes("20:45"), "min_dur":45},
        "Matthew":  {"location":"Russian Hill",   "avail_start":time_to_minutes("15:45"), "avail_end":time_to_minutes("21:45"), "min_dur":75},
    }

    names = list(persons.keys())

    opt = Optimize()

    start_vars = {n: Int(f"start_{n}") for n in names}
    end_vars   = {n: Int(f"end_{n}") for n in names}
    meet_vars  = {n: Bool(f"meet_{n}") for n in names}

    # Variable bounds and availability constraints
    for n in names:
        s = start_vars[n]
        e = end_vars[n]
        info = persons[n]
        opt.add(s >= 0, s <= 24*60, e >= 0, e <= 24*60)
        # If meeting occurs, must fit within availability and meet minimum duration
        opt.add(Implies(meet_vars[n], And(
            s >= info["avail_start"],
            e <= info["avail_end"],
            e > s,
            e - s >= info["min_dur"]
        )))
        # If not meeting, clamp to zero to keep model clean (optional)
        opt.add(Implies(Not(meet_vars[n]), And(s == 0, e == 0)))

        # Travel from starting city (Bayview) at arrival_time
        # If meeting occurs, cannot start before travel time from Bayview
        loc = persons[n]["location"]
        opt.add(Implies(meet_vars[n], s >= arrival_time + travel[(start_city, loc)]))

    # Pairwise non-overlap with travel time using ordering booleans
    order_vars = {}
    for i in range(len(names)):
        for j in range(i+1, len(names)):
            a = names[i]
            b = names[j]
            o_ab = Bool(f"order_{a}_{b}")
            order_vars[(a,b)] = o_ab
            sa, ea, la = start_vars[a], end_vars[a], persons[a]["location"]
            sb, eb, lb = start_vars[b], end_vars[b], persons[b]["location"]
            # If both meetings happen and a before b
            opt.add(Implies(And(meet_vars[a], meet_vars[b], o_ab),
                            ea + travel[(la, lb)] <= sb))
            # If both meetings happen and b before a (i.e., not o_ab)
            opt.add(Implies(And(meet_vars[a], meet_vars[b], Not(o_ab)),
                            eb + travel[(lb, la)] <= sa))

    # Objective: maximize number of meetings, then maximize total meeting minutes
    meet_count = Sum([If(meet_vars[n], 1, 0) for n in names])
    total_minutes = Sum([If(meet_vars[n], end_vars[n] - start_vars[n], 0) for n in names])
    opt.maximize(meet_count)
    opt.maximize(total_minutes)

    if opt.check() != sat:
        print(json.dumps({"itinerary": []}))
        return

    m = opt.model()

    itinerary = []
    for n in names:
        if is_true(m.eval(meet_vars[n])):
            s = m.eval(start_vars[n]).as_long()
            e = m.eval(end_vars[n]).as_long()
            itinerary.append({
                "action": "meet",
                "location": persons[n]["location"],
                "person": n,
                "start_time": minutes_to_time(s),
                "end_time": minutes_to_time(e),
            })

    # Sort by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))

    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()