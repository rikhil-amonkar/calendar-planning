import json
from z3 import *

def main():
    # Define city identifiers, names, and required durations
    city_names = {
        0: "Paris",
        1: "Warsaw",
        2: "Krakow",
        3: "Tallinn",
        4: "Riga",
        5: "Copenhagen",
        6: "Helsinki",
        7: "Oslo",
        8: "Santorini",
        9: "Lyon"
    }
    durations = {
        0: 5,  # Paris
        1: 2,  # Warsaw
        2: 2,  # Krakow
        3: 2,  # Tallinn
        4: 2,  # Riga
        5: 5,  # Copenhagen
        6: 5,  # Helsinki
        7: 5,  # Oslo
        8: 2,  # Santorini
        9: 4   # Lyon
    }
    num_segments = 10  # 10 cities visited

    solver = Solver()

    # Define itinerary as a permutation of the 10 cities.
    itinerary = [Int(f"city_{i}") for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(itinerary[i] >= 0, itinerary[i] < num_segments)
    solver.add(Distinct(itinerary))

    # Define start day S[i] for each city segment.
    S = [Int(f"S_{i}") for i in range(num_segments)]
    for i in range(num_segments):
        solver.add(S[i] >= 1, S[i] <= 25)

    # Helper: city-specific duration given a city variable.
    def city_duration(city_var):
        return If(city_var == 0, durations[0],
               If(city_var == 1, durations[1],
               If(city_var == 2, durations[2],
               If(city_var == 3, durations[3],
               If(city_var == 4, durations[4],
               If(city_var == 5, durations[5],
               If(city_var == 6, durations[6],
               If(city_var == 7, durations[7],
               If(city_var == 8, durations[8],
               If(city_var == 9, durations[9], 0))))))))))

    # Scheduling constraints:
    # The trip begins on Day 1.
    solver.add(S[0] == 1)
    # If you fly from city A to city B on day X then day X counts for both.
    # Therefore, the next segment starts on: previous start + (duration of previous city) - 1.
    for i in range(num_segments - 1):
        solver.add(S[i+1] == S[i] + city_duration(itinerary[i]) - 1)
    # The end of the final segment must equal Day 25.
    solver.add(S[num_segments - 1] + city_duration(itinerary[num_segments - 1]) - 1 == 25)

    # Flight connectivity constraints:
    # Define allowed direct flights as per the given list.
    def allowed_flight(a, b):
        # a and b are city ID Z3 ints.
        rules = []
        # Symmetric (bidirectional) flights:
        symmetric_pairs = [
            (1, 4),  # Warsaw <-> Riga
            (1, 3),  # Warsaw <-> Tallinn
            (5, 6),  # Copenhagen <-> Helsinki
            (9, 0),  # Lyon <-> Paris
            (5, 1),  # Copenhagen <-> Warsaw
            (9, 7),  # Lyon <-> Oslo
            (0, 7),  # Paris <-> Oslo
            (0, 4),  # Paris <-> Riga
            (2, 6),  # Krakow <-> Helsinki
            (0, 3),  # Paris <-> Tallinn
            (7, 4),  # Oslo <-> Riga
            (2, 1),  # Krakow <-> Warsaw
            (0, 6),  # Paris <-> Helsinki
            (5, 2),  # Copenhagen <-> Krakow
            (5, 8),  # Copenhagen <-> Santorini
            (6, 1),  # Helsinki <-> Warsaw
            (6, 4),  # Helsinki <-> Riga
            (5, 4),  # Copenhagen <-> Riga
            (0, 2),  # Paris <-> Krakow
            (5, 7),  # Copenhagen <-> Oslo
            (7, 3),  # Oslo <-> Tallinn
            (7, 6),  # Oslo <-> Helsinki
            (5, 3),  # Copenhagen <-> Tallinn
            (7, 2),  # Oslo <-> Krakow
            (6, 3),  # Helsinki <-> Tallinn
            (0, 5),  # Paris <-> Copenhagen
            (0, 1),  # Paris <-> Warsaw
            (7, 1)   # Oslo <-> Warsaw
        ]
        for (x, y) in symmetric_pairs:
            rules.append(Or(And(a == x, b == y), And(a == y, b == x)))
        # Directed flights (only one way):
        rules.append(And(a == 4, b == 3))  # Riga -> Tallinn only
        rules.append(And(a == 8, b == 7))  # Santorini -> Oslo only
        return Or(rules)

    # For each consecutive pair in the itinerary, ensure a direct flight exists.
    for i in range(num_segments - 1):
        solver.add(allowed_flight(itinerary[i], itinerary[i+1]))

    # Event constraints:
    # Paris: 5 days with a friend meetup between Day 4 and Day 8.
    # The 5-day Paris interval [S, S+4] must intersect with [4,8] => S <= 8.
    for i in range(num_segments):
        solver.add(Implies(itinerary[i] == 0, S[i] <= 8))
    # Krakow: 2 days with a workshop between Day 17 and Day 18.
    # [S, S+1] must intersect with [17,18] => S <= 18 and S+1 >= 17, i.e. S in [16,18].
    for i in range(num_segments):
        solver.add(Implies(itinerary[i] == 2, And(S[i] >= 16, S[i] <= 18)))
    # Helsinki: 5 days with a friend meetup between Day 18 and Day 22.
    # [S, S+4] must intersect with [18,22] => S <= 22 and S+4 >= 18, i.e. S in [14,22].
    for i in range(num_segments):
        solver.add(Implies(itinerary[i] == 6, And(S[i] >= 14, S[i] <= 22)))
    # Santorini: 2 days with relatives visiting between Day 12 and Day 13.
    # [S, S+1] must intersect with [12,13] => S in [11,13].
    for i in range(num_segments):
        solver.add(Implies(itinerary[i] == 8, And(S[i] >= 11, S[i] <= 13)))
    # Riga: 2 days with a wedding between Day 23 and Day 24.
    # [S, S+1] must intersect with [23,24] => S in [22,24].
    for i in range(num_segments):
        solver.add(Implies(itinerary[i] == 4, And(S[i] >= 22, S[i] <= 24)))

    # Check for a solution.
    if solver.check() == sat:
        model = solver.model()
        result_itinerary = []
        for i in range(num_segments):
            city_id = model.evaluate(itinerary[i]).as_long()
            start_day = model.evaluate(S[i]).as_long()
            # Compute the end day for each segment: start + duration - 1.
            city_dur = durations[city_id]
            end_day = start_day + city_dur - 1
            result_itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_id]
            })
        output = {"itinerary": result_itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()