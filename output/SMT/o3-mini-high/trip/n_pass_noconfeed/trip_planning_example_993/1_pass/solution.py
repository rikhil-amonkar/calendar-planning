from z3 import *
import json

def main():
    solver = Solver()

    # There are 7 segments (one per city visit)
    # x[i] is the city index for segment i:
    # 0: Riga, 1: Frankfurt, 2: Amsterdam, 3: Vilnius, 4: London, 5: Stockholm, 6: Bucharest
    x = [Int(f"x_{i}") for i in range(7)]
    # s[i] and e[i] denote the start and end day for segment i.
    s = [Int(f"s_{i}") for i in range(7)]
    e = [Int(f"e_{i}") for i in range(7)]
    
    # Event day variables (for events that must occur during the visit to a specific city)
    meet_amsterdam = Int("meet_amsterdam")
    workshop = Int("workshop")
    wedding = Int("wedding")
    
    # Mapping for city names and required durations
    cities = {
        0: "Riga",
        1: "Frankfurt",
        2: "Amsterdam",
        3: "Vilnius",
        4: "London",
        5: "Stockholm",
        6: "Bucharest"
    }
    durations = {
        0: 2,  # Riga for 2 days
        1: 3,  # Frankfurt for 3 days
        2: 2,  # Amsterdam for 2 days
        3: 5,  # Vilnius for 5 days
        4: 2,  # London for 2 days
        5: 3,  # Stockholm for 3 days
        6: 4   # Bucharest for 4 days
    }
    
    # Domain constraints for cities in each segment (each city appears exactly once)
    for i in range(7):
        solver.add(x[i] >= 0, x[i] <= 6)
    solver.add(Distinct(x))
    
    # Domain constraints on days for each segment (days 1 to 15)
    for i in range(7):
        solver.add(s[i] >= 1, s[i] <= 15)
        solver.add(e[i] >= 1, e[i] <= 15)
    
    # Domain constraints for event days:
    solver.add(meet_amsterdam >= 2, meet_amsterdam <= 3)  # Friend meeting in Amsterdam on day 2 or 3
    solver.add(workshop >= 7, workshop <= 11)             # Workshop in Vilnius between day 7 and 11
    solver.add(wedding >= 13, wedding <= 15)                # Wedding in Stockholm between day 13 and 15
    
    # Chain time constraints:
    # The trip starts on day 1.
    solver.add(s[0] == 1)
    # When flying from one city to the next the flight day is counted in both segments.
    # We enforce that the next segment starts exactly on the day the previous one ends.
    for i in range(6):
        solver.add(s[i+1] == e[i])
    # The trip must finish on day 15.
    solver.add(e[6] == 15)
    
    # Duration constraints for each segment based on the city visited.
    # The duration in a city is computed as: (e - s + 1) == required days.
    for i in range(7):
        solver.add(
            If(x[i] == 0, e[i] - s[i] + 1 == durations[0],
            If(x[i] == 1, e[i] - s[i] + 1 == durations[1],
            If(x[i] == 2, e[i] - s[i] + 1 == durations[2],
            If(x[i] == 3, e[i] - s[i] + 1 == durations[3],
            If(x[i] == 4, e[i] - s[i] + 1 == durations[4],
            If(x[i] == 5, e[i] - s[i] + 1 == durations[5],
            If(x[i] == 6, e[i] - s[i] + 1 == durations[6],
               True)))))))
    
    # Flight graph: allowed direct flights between cities (bidirectional).
    # Each tuple represents a valid flight between two cities.
    valid_flights = [
        (4, 2), (2, 4),    # London and Amsterdam
        (3, 1), (1, 3),    # Vilnius and Frankfurt
        (0, 3), (3, 0),    # Riga and Vilnius (from Riga to Vilnius is given, assume reverse is possible)
        (0, 5), (5, 0),    # Riga and Stockholm
        (4, 6), (6, 4),    # London and Bucharest
        (2, 5), (5, 2),    # Amsterdam and Stockholm
        (2, 1), (1, 2),    # Amsterdam and Frankfurt
        (1, 5), (5, 1),    # Frankfurt and Stockholm
        (6, 0), (0, 6),    # Bucharest and Riga
        (2, 0), (0, 2),    # Amsterdam and Riga
        (2, 6), (6, 2),    # Amsterdam and Bucharest
        (0, 1), (1, 0),    # Riga and Frankfurt
        (6, 1), (1, 6),    # Bucharest and Frankfurt
        (4, 1), (1, 4),    # London and Frankfurt
        (4, 5), (5, 4),    # London and Stockholm
        (2, 3), (3, 2)     # Amsterdam and Vilnius
    ]
    
    # For each flight leg (between segment i and i+1) ensure there is a direct flight.
    for i in range(6):
        flight_options = []
        for (a, b) in valid_flights:
            flight_options.append(And(x[i] == a, x[i+1] == b))
        solver.add(Or(flight_options))
    
    # Event constraints:
    # In the segment where Amsterdam is visited (city id 2), the meeting must occur during that segment.
    for i in range(7):
        solver.add(Implies(x[i] == 2, And(s[i] <= meet_amsterdam, meet_amsterdam <= e[i])))
    # In the segment where Vilnius is visited (city id 3), the workshop must occur during that segment.
    for i in range(7):
        solver.add(Implies(x[i] == 3, And(s[i] <= workshop, workshop <= e[i])))
    # In the segment where Stockholm is visited (city id 5), the wedding must occur during that segment.
    for i in range(7):
        solver.add(Implies(x[i] == 5, And(s[i] <= wedding, wedding <= e[i])))

    # Solve the SMT problem.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(7):
            city_id = model[x[i]].as_long()
            city_name = cities[city_id]
            start_day = model[s[i]].as_long()
            end_day = model[e[i]].as_long()
            itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city_name})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()