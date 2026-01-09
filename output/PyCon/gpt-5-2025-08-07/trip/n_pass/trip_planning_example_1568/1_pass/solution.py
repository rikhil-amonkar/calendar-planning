import json
from constraint import Problem, AllDifferentConstraint

def build_adjacency():
    adj = {}
    def add_city(c):
        if c not in adj:
            adj[c] = set()
    def add_pair(a, b, undirected=True):
        add_city(a); add_city(b)
        adj[a].add(b)
        if undirected:
            adj[b].add(a)

    # List all given direct flights
    add_pair("Riga", "Stockholm")
    add_pair("Stockholm", "Brussels")
    add_pair("Istanbul", "Munich")
    add_pair("Istanbul", "Riga")
    add_pair("Prague", "Split")
    add_pair("Vienna", "Brussels")
    add_pair("Vienna", "Riga")
    add_pair("Split", "Stockholm")
    add_pair("Munich", "Amsterdam")
    add_pair("Split", "Amsterdam")
    add_pair("Amsterdam", "Stockholm")
    add_pair("Amsterdam", "Riga")
    add_pair("Vienna", "Stockholm")
    add_pair("Vienna", "Istanbul")
    add_pair("Vienna", "Seville")
    add_pair("Istanbul", "Amsterdam")
    add_pair("Munich", "Brussels")
    add_pair("Prague", "Munich")
    # directed: from Riga to Munich
    add_pair("Riga", "Munich", undirected=False)
    add_pair("Prague", "Amsterdam")
    add_pair("Prague", "Brussels")
    add_pair("Prague", "Istanbul")
    add_pair("Istanbul", "Stockholm")
    add_pair("Vienna", "Prague")
    add_pair("Munich", "Split")
    add_pair("Vienna", "Amsterdam")
    add_pair("Prague", "Stockholm")
    add_pair("Brussels", "Seville")
    add_pair("Munich", "Stockholm")
    add_pair("Istanbul", "Brussels")
    add_pair("Amsterdam", "Seville")
    add_pair("Vienna", "Split")
    add_pair("Munich", "Seville")
    add_pair("Riga", "Brussels")
    add_pair("Prague", "Riga")
    add_pair("Vienna", "Munich")

    return adj

def main():
    cities = [
        "Riga","Stockholm","Brussels","Istanbul",
        "Munich","Amsterdam","Split","Seville",
        "Vienna","Prague"
    ]
    durations = {
        "Riga": 2,
        "Stockholm": 2,
        "Brussels": 2,
        "Istanbul": 2,
        "Munich": 2,
        "Amsterdam": 3,
        "Split": 3,
        "Seville": 3,
        "Vienna": 5,
        "Prague": 5
    }

    adj = build_adjacency()

    problem = Problem()

    # Variables: City at each position 1..10, and Start day at each position
    positions = list(range(1, 11))
    city_vars = [f"City_{p}" for p in positions]
    start_vars = [f"Start_{p}" for p in positions]

    # Domains
    for cv in city_vars:
        problem.addVariable(cv, cities)
    for sv in start_vars:
        problem.addVariable(sv, range(1, 21))

    # All cities must be used exactly once
    problem.addConstraint(AllDifferentConstraint(), city_vars)

    # The trip starts on Day 1 for the first position
    problem.addConstraint(lambda s: s == 1, ("Start_1",))

    # Chain constraints: adjacency and start times connect with 1-day overlap
    def chain_constraint(c1, c2, s1, s2):
        # adjacency
        if c1 not in adj or c2 not in adj[c1]:
            return False
        # start alignment with overlap day counted in both
        return s2 == s1 + durations[c1] - 1

    for p in range(1, 10):
        problem.addConstraint(chain_constraint, (f"City_{p}", f"City_{p+1}", f"Start_{p}", f"Start_{p+1}"))

    # The trip ends on Day 20
    def end_day_constraint(c, s):
        return s + durations[c] - 1 == 20
    problem.addConstraint(end_day_constraint, ("City_10", "Start_10"))

    # Fixed date constraints and specific city requirements
    def city_time_constraint(city, start):
        # Ensure segments fit within 1..20 (implicit, but keep consistent)
        if start < 1 or start > 20:
            return False
        end = start + durations[city] - 1
        if end < 1 or end > 20:
            return False

        # Specific constraints:
        # Prague: must be in Prague days 5-9 (duration 5 => start must be 5)
        if city == "Prague" and start != 5:
            return False

        # Split: must be days 11-13
        if city == "Split" and start != 11:
            return False

        # Riga: meet friends between day 15 and 16 => duration 2 => start 15
        if city == "Riga" and start != 15:
            return False

        # Stockholm: conference day 16-17 => duration 2 => start 16
        if city == "Stockholm" and start != 16:
            return False

        # Vienna: meet friend between day 1 and 5 => interval must intersect [1,5]
        if city == "Vienna":
            if not (start <= 5 and end >= 1):
                return False

        # Other cities: duration already enforced globally
        return True

    for p in positions:
        problem.addConstraint(city_time_constraint, (f"City_{p}", f"Start_{p}"))

    # Solve
    solution = problem.getSolution()

    if not solution:
        print(json.dumps({"error": "No feasible itinerary found"}))
        return

    # Build itinerary in order
    itinerary = []
    for p in positions:
        city = solution[f"City_{p}"]
        start = solution[f"Start_{p}"]
        end = start + durations[city] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()