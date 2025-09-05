from z3 import *
import json

def main():
    # There are 7 cities with fixed durations
    # City codes: 0: Berlin, 1: Split, 2: Bucharest, 3: Riga, 4: Lisbon, 5: Tallinn, 6: Lyon
    durations = {0: 5, 1: 3, 2: 3, 3: 5, 4: 3, 5: 4, 6: 5}
    city_names = {0: "Berlin", 1: "Split", 2: "Bucharest", 3: "Riga", 4: "Lisbon", 5: "Tallinn", 6: "Lyon"}
    
    # Total segments equals 7 (each city is visited once)
    segments = 7

    # Create solver
    solver = Solver()

    # Decision variables:
    # city_vars[i] will hold the city code for segment i. (Permutation of {0,...,6} with Berlin fixed at position 0)
    city_vars = [Int(f"city_{i}") for i in range(segments)]
    # start_vars[i] is the start day of segment i,
    # end_vars[i] is the end day of segment i.
    start_vars = [Int(f"start_{i}") for i in range(segments)]
    end_vars = [Int(f"end_{i}") for i in range(segments)]

    # Domain constraints for city indices: they are between 0 and 6.
    for cv in city_vars:
        solver.add(And(cv >= 0, cv <= 6))
    # All cities must be distinct (permutation)
    solver.add(Distinct(city_vars))
    # Berlin must be the first city (Berlin has code 0)
    solver.add(city_vars[0] == 0)

    # Define a function to return the duration corresponding to a city variable.
    def duration(city):
        return If(city == 0, durations[0],
               If(city == 1, durations[1],
               If(city == 2, durations[2],
               If(city == 3, durations[3],
               If(city == 4, durations[4],
               If(city == 5, durations[5],
               If(city == 6, durations[6], 0))))))

    # Timing constraints:
    # Trip starts on day 1. If you fly from one city to the next on the same day,
    # then that day is counted for both segments.
    solver.add(start_vars[0] == 1)
    for i in range(segments):
        # End day of segment i (always start_i + duration -1)
        solver.add(end_vars[i] == start_vars[i] + duration(city_vars[i]) - 1)
        if i > 0:
            # When flying from segment i-1 to i, the departure/arrival happens on the same day:
            solver.add(start_vars[i] == end_vars[i-1])
    # The final city must end on day 22.
    solver.add(end_vars[segments - 1] == 22)

    # Special date constraints:
    # Bucharest (code 2) must be visited during days that include at least one day between 13 and 15.
    # For a 3-day visit, this is equivalent to starting no later than day 15 and ending no earlier than day 13:
    # Since end = start+2, we require start ∈ [11, 15] (because 11+2=13).
    for i in range(segments):
        solver.add(Implies(city_vars[i] == 2, And(start_vars[i] >= 11, start_vars[i] <= 15)))
        
    # Lyon (code 6) must include the wedding between days 7 and 11.
    # For a 5-day stay, this is ensured if the segment starts on or before day 11 and (start+4) is on or after day 7.
    for i in range(segments):
        solver.add(Implies(city_vars[i] == 6, And(start_vars[i] <= 11, start_vars[i] + 4 >= 7)))

    # Allowed direct flights between cities.
    # Each flight leg is only permitted if there is a direct connection.
    # List of allowed pairs using city codes:
    # (Berlin, Lisbon): (0,4) and (Lisbon, Berlin): (4,0)
    # (Berlin, Riga): (0,3) and (Riga, Berlin): (3,0)
    # (Berlin, Split): (0,1) and (Split, Berlin): (1,0)
    # (Berlin, Tallinn): (0,5) and (Tallinn, Berlin): (5,0)
    # (Lisbon, Bucharest): (4,2) and (Bucharest, Lisbon): (2,4)
    # (Bucharest, Riga): (2,3) and (Riga, Bucharest): (3,2)
    # (Split, Lyon): (1,6) and (Lyon, Split): (6,1)
    # (Lisbon, Riga): (4,3) and (Riga, Lisbon): (3,4)
    # (Lyon, Lisbon): (6,4) and (Lisbon, Lyon): (4,6)
    # (Lyon, Bucharest): (6,2) and (Bucharest, Lyon): (2,6)
    # Also: from Riga to Tallinn is allowed (3,5) [only one-way].
    allowed_pairs = [
        (0, 4), (4, 0),
        (0, 3), (3, 0),
        (0, 1), (1, 0),
        (0, 5), (5, 0),
        (4, 2), (2, 4),
        (2, 3), (3, 2),
        (1, 6), (6, 1),
        (4, 3), (3, 4),
        (6, 4), (4, 6),
        (6, 2), (2, 6),
        (3, 5)
    ]
    
    # For each consecutive pair in the itinerary, enforce the existence of a direct flight.
    for i in range(segments - 1):
        a = city_vars[i]
        b = city_vars[i + 1]
        flight_possible = []
        for (p, q) in allowed_pairs:
            flight_possible.append(And(a == p, b == q))
        solver.add(Or(flight_possible))

    # Find a solution.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(segments):
            s_day = model[start_vars[i]].as_long()
            e_day = model[end_vars[i]].as_long()
            city_code = model[city_vars[i]].as_long()
            itinerary.append({
                "day_range": f"Day {s_day}-{e_day}",
                "place": city_names[city_code]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no solution is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()