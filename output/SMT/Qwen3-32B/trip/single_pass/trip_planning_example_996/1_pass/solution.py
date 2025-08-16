from z3 import *
import json

def main():
    cities = ['Mykonos', 'Prague', 'Valencia', 'Riga', 'Zurich', 'Bucharest', 'Nice']
    city_durations = [3, 3, 5, 5, 5, 5, 2]  # Corresponding to cities list

    allowed_transitions = {
        (0, 6), (6, 0),  # Mykonos-Nice
        (0, 4), (4, 0),  # Mykonos-Zurich
        (1, 5), (5, 1),  # Prague-Bucharest
        (2, 5), (5, 2),  # Valencia-Bucharest
        (4, 1), (1, 4),  # Zurich-Prague
        (3, 6), (6, 3),  # Riga-Nice
        (4, 3), (3, 4),  # Zurich-Riga
        (4, 5), (5, 4),  # Zurich-Bucharest
        (4, 2), (2, 4),  # Zurich-Valencia
        (5, 3), (3, 5),  # Bucharest-Riga
        (1, 3), (3, 1),  # Prague-Riga
        (1, 2), (2, 1),  # Prague-Valencia
        (4, 6), (6, 4),  # Zurich-Nice
    }

    s = Solver()

    seq = [Int(f'seq_{i}') for i in range(7)]
    start_days = [Int(f'start_day_{i}') for i in range(7)]

    # Constraints for seq to be a permutation of 0-6
    for i in range(7):
        s.add(And(0 <= seq[i], seq[i] <= 6))
    s.add(Distinct(seq))

    # Allowed transitions between consecutive cities
    for i in range(6):
        transitions = []
        for a, b in allowed_transitions:
            transitions.append(And(seq[i] == a, seq[i+1] == b))
        s.add(Or(transitions))

    # Start day constraints
    s.add(start_days[0] == 1)
    for i in range(6):
        duration_i = If(seq[i] == 0, 3,
            If(seq[i] == 1, 3,
                If(seq[i] == 2, 5,
                    If(seq[i] == 3, 5,
                        If(seq[i] == 4, 5,
                            If(seq[i] == 5, 5, 2)
                        )
                    )
                )
            )
        )
        s.add(start_days[i+1] == start_days[i] + duration_i - 1)

    # Mykonos and Prague constraints
    for i in range(7):
        s.add(Or(seq[i] != 0, start_days[i] <= 3))
        s.add(Or(seq[i] != 1, And(start_days[i] >= 5, start_days[i] <= 9)))

    if s.check() == sat:
        model = s.model()
        seq_values = [model.eval(seq[i]).as_long() for i in range(7)]
        start_days_values = [model.eval(start_days[i]).as_long() for i in range(7)]

        itinerary = []
        for i in range(7):
            city_index = seq_values[i]
            city_name = cities[city_index]
            start = start_days_values[i]
            duration = city_durations[city_index]
            end = start + duration - 1
            for day in range(start, end + 1):
                itinerary.append({day: city_name})

        # Sort itinerary by day
        itinerary.sort(key=lambda x: list(x.keys())[0])

        # Build JSON output
        json_output = {'itinerary': itinerary}
        print(json.dumps(json_output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()