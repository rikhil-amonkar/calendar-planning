# Solve the SF one-day meetups optimization with Z3 (maximize number of friends met)
# The model encodes a TSP-with-time-windows-like problem with pairwise non-overlap and travel times.

from z3 import Optimize, Int, Sum, If

def hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def solve():
    # Constants
    M = 10**6
    START_TIME = 9*60  # 09:00 at Financial District

    # Districts
    FD = "Financial District"
    districts = [
        "Financial District",
        "Fisherman's Wharf",
        "Presidio",
        "Bayview",
        "Haight-Ashbury",
        "Russian Hill",
        "The Castro",
        "Marina District",
        "Richmond District",
        "Union Square",
        "Sunset District",
    ]

    # Travel times (minutes) as provided
    T = {}
    def set_t(a, b, v):
        T[(a,b)] = v

    # Fill travel matrix (all directed pairs from prompt)
    set_t("Financial District", "Fisherman's Wharf", 10)
    set_t("Financial District", "Presidio", 22)
    set_t("Financial District", "Bayview", 19)
    set_t("Financial District", "Haight-Ashbury", 19)
    set_t("Financial District", "Russian Hill", 11)
    set_t("Financial District", "The Castro", 20)
    set_t("Financial District", "Marina District", 15)
    set_t("Financial District", "Richmond District", 21)
    set_t("Financial District", "Union Square", 9)
    set_t("Financial District", "Sunset District", 30)

    set_t("Fisherman's Wharf", "Financial District", 11)
    set_t("Fisherman's Wharf", "Presidio", 17)
    set_t("Fisherman's Wharf", "Bayview", 26)
    set_t("Fisherman's Wharf", "Haight-Ashbury", 22)
    set_t("Fisherman's Wharf", "Russian Hill", 7)
    set_t("Fisherman's Wharf", "The Castro", 27)
    set_t("Fisherman's Wharf", "Marina District", 9)
    set_t("Fisherman's Wharf", "Richmond District", 18)
    set_t("Fisherman's Wharf", "Union Square", 13)
    set_t("Fisherman's Wharf", "Sunset District", 27)

    set_t("Presidio", "Financial District", 23)
    set_t("Presidio", "Fisherman's Wharf", 19)
    set_t("Presidio", "Bayview", 31)
    set_t("Presidio", "Haight-Ashbury", 15)
    set_t("Presidio", "Russian Hill", 14)
    set_t("Presidio", "The Castro", 21)
    set_t("Presidio", "Marina District", 11)
    set_t("Presidio", "Richmond District", 7)
    set_t("Presidio", "Union Square", 22)
    set_t("Presidio", "Sunset District", 15)

    set_t("Bayview", "Financial District", 19)
    set_t("Bayview", "Fisherman's Wharf", 25)
    set_t("Bayview", "Presidio", 32)
    set_t("Bayview", "Haight-Ashbury", 19)
    set_t("Bayview", "Russian Hill", 23)
    set_t("Bayview", "The Castro", 19)
    set_t("Bayview", "Marina District", 27)
    set_t("Bayview", "Richmond District", 25)
    set_t("Bayview", "Union Square", 18)
    set_t("Bayview", "Sunset District", 23)

    set_t("Haight-Ashbury", "Financial District", 21)
    set_t("Haight-Ashbury", "Fisherman's Wharf", 23)
    set_t("Haight-Ashbury", "Presidio", 15)
    set_t("Haight-Ashbury", "Bayview", 18)
    set_t("Haight-Ashbury", "Russian Hill", 17)
    set_t("Haight-Ashbury", "The Castro", 6)
    set_t("Haight-Ashbury", "Marina District", 17)
    set_t("Haight-Ashbury", "Richmond District", 10)
    set_t("Haight-Ashbury", "Union Square", 19)
    set_t("Haight-Ashbury", "Sunset District", 15)

    set_t("Russian Hill", "Financial District", 11)
    set_t("Russian Hill", "Fisherman's Wharf", 7)
    set_t("Russian Hill", "Presidio", 14)
    set_t("Russian Hill", "Bayview", 23)
    set_t("Russian Hill", "Haight-Ashbury", 17)
    set_t("Russian Hill", "The Castro", 21)
    set_t("Russian Hill", "Marina District", 7)
    set_t("Russian Hill", "Richmond District", 14)
    set_t("Russian Hill", "Union Square", 10)
    set_t("Russian Hill", "Sunset District", 23)

    set_t("The Castro", "Financial District", 21)
    set_t("The Castro", "Fisherman's Wharf", 24)
    set_t("The Castro", "Presidio", 20)
    set_t("The Castro", "Bayview", 19)
    set_t("The Castro", "Haight-Ashbury", 6)
    set_t("The Castro", "Russian Hill", 18)
    set_t("The Castro", "Marina District", 21)
    set_t("The Castro", "Richmond District", 16)
    set_t("The Castro", "Union Square", 19)
    set_t("The Castro", "Sunset District", 17)

    set_t("Marina District", "Financial District", 17)
    set_t("Marina District", "Fisherman's Wharf", 10)
    set_t("Marina District", "Presidio", 10)
    set_t("Marina District", "Bayview", 27)
    set_t("Marina District", "Haight-Ashbury", 16)
    set_t("Marina District", "Russian Hill", 8)
    set_t("Marina District", "The Castro", 22)  # Given 21-> maybe 21? Prompt says 21 from The Castro to Marina; here we need Marina->The Castro = 22? Not provided; use 21? But prompt lists "Marina District to The Castro: 22."
    set_t("Marina District", "Richmond District", 11)
    set_t("Marina District", "Union Square", 16)
    set_t("Marina District", "Sunset District", 19)

    set_t("Richmond District", "Financial District", 22)
    set_t("Richmond District", "Fisherman's Wharf", 18)
    set_t("Richmond District", "Presidio", 7)
    set_t("Richmond District", "Bayview", 27)
    set_t("Richmond District", "Haight-Ashbury", 10)
    set_t("Richmond District", "Russian Hill", 13)
    set_t("Richmond District", "The Castro", 16)
    set_t("Richmond District", "Marina District", 9)
    set_t("Richmond District", "Union Square", 21)
    set_t("Richmond District", "Sunset District", 11)

    set_t("Union Square", "Financial District", 9)
    set_t("Union Square", "Fisherman's Wharf", 15)
    set_t("Union Square", "Presidio", 24)
    set_t("Union Square", "Bayview", 15)
    set_t("Union Square", "Haight-Ashbury", 18)
    set_t("Union Square", "Russian Hill", 13)
    set_t("Union Square", "The Castro", 17)
    set_t("Union Square", "Marina District", 18)
    set_t("Union Square", "Richmond District", 20)
    set_t("Union Square", "Sunset District", 27)

    set_t("Sunset District", "Financial District", 30)
    set_t("Sunset District", "Fisherman's Wharf", 29)
    set_t("Sunset District", "Presidio", 16)
    set_t("Sunset District", "Bayview", 22)
    set_t("Sunset District", "Haight-Ashbury", 15)
    set_t("Sunset District", "Russian Hill", 24)
    set_t("Sunset District", "The Castro", 17)
    set_t("Sunset District", "Marina District", 21)
    set_t("Sunset District", "Richmond District", 12)
    set_t("Sunset District", "Union Square", 30)

    # Friends data
    def tm(h, m): return h*60 + m
    friends = [
        # name, district, earliest, latest, duration
        ("Mark", "Fisherman's Wharf", tm(8,15), tm(10,0), 30),
        ("Stephanie", "Presidio", tm(12,15), tm(15,0), 75),
        ("Betty", "Bayview", tm(7,15), tm(20,30), 15),
        ("Lisa", "Haight-Ashbury", tm(15,30), tm(18,30), 45),
        ("William", "Russian Hill", tm(18,45), tm(20,0), 60),
        ("Brian", "The Castro", tm(9,15), tm(13,15), 30),
        ("Joseph", "Marina District", tm(10,45), tm(15,0), 90),
        ("Ashley", "Richmond District", tm(9,45), tm(11,15), 45),
        ("Patricia", "Union Square", tm(16,30), tm(20,0), 120),
        ("Karen", "Sunset District", tm(16,30), tm(22,0), 105),
    ]

    n = len(friends)
    name = [f[0] for f in friends]
    loc = [f[1] for f in friends]
    a = [f[2] for f in friends]
    b = [f[3] for f in friends]
    d = [f[4] for f in friends]

    opt = Optimize()

    # Variables
    t = [Int(f"t_{i}") for i in range(n)]                  # start time
    s = [Int(f"s_{i}") for i in range(n)]                  # 0/1 select
    z = [[Int(f"z_{i}_{j}") if i!=j else Int(f"z_{i}_{j}") for j in range(n)] for i in range(n)]  # precedence

    # Domains
    for i in range(n):
        opt.add(s[i] >= 0, s[i] <= 1)
        opt.add(t[i] >= 0, t[i] <= 24*60)
        # Availability if selected
        opt.add(t[i] >= a[i] - M*(1 - s[i]))
        opt.add(t[i] <= (b[i] - d[i]) + M*(1 - s[i]))
        # Start from FD feasibility lower bound
        opt.add(t[i] >= START_TIME + T[(FD, loc[i])] - M*(1 - s[i)])

    # Pairwise non-overlap and travel precedence
    for i in range(n):
        for j in range(n):
            if i == j: 
                opt.add(z[i][j] == 0)
                continue
            opt.add(z[i][j] >= 0, z[i][j] <= 1)
            opt.add(z[i][j] <= s[i])
            opt.add(z[i][j] <= s[j])
    for i in range(n):
        for j in range(i+1, n):
            # Exactly one precedence if both selected, else 0
            opt.add(z[i][j] + z[j][i] <= 1)
            opt.add(z[i][j] + z[j][i] >= s[i] + s[j] - 1)
            # Time feasibility with travel
            opt.add(t[j] >= t[i] + d[i] + T[(loc[i], loc[j])] - M*(1 - z[i][j]))
            opt.add(t[i] >= t[j] + d[j] + T[(loc[j], loc[i])] - M*(1 - z[j][i]))

    # Objective: maximize number of friends met
    total = Sum(s)
    opt.maximize(total)

    # Optional secondary tie-breakers (not required): minimize end time of day
    last_end = Int("last_end")
    opt.add(last_end >= 0)
    for i in range(n):
        # last_end >= t[i] + d[i] if selected, else no effect
        opt.add(last_end >= t[i] + d[i] - M*(1 - s[i]))
    opt.minimize(last_end)

    if opt.check() != 1:
        return {"itinerary": []}

    m = opt.model()

    # Extract selected meetings and sort by start time
    sched = []
    for i in range(n):
        if m.eval(s[i]).as_long() == 1:
            st = m.eval(t[i]).as_long()
            en = st + d[i]
            sched.append((st, en, name[i]))
    sched.sort()

    itinerary = []
    for st, en, nm in sched:
        itinerary.append({
            "action": "meet",
            "person": nm,
            "start_time": hhmm(st),
            "end_time": hhmm(en)
        })

    return {"itinerary": itinerary}

if __name__ == "__main__":
    import json
    result = solve()
    print(json.dumps(result))