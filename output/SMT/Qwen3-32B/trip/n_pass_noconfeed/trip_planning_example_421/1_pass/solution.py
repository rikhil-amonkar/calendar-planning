import z3
import json

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    durations = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }

    s = z3.Solver()

    X = z3.Int('X')
    Y = z3.Int('Y')
    Z = z3.Int('Z')

    s.add(z3.And(X >= 1, X <= 3))
    s.add(z3.And(Y >= 1, Y <= 3))
    s.add(z3.And(Z >= 1, Z <= 3))
    s.add(z3.Distinct(X, Y, Z))

    s.add(z3.Or(X == 2, X == 3))  # Direct flights from Nice to Dublin (2) or Lyon (3)

    allowed_middle_pairs = [
        (1, 2), (2, 1), (2, 3), (3, 2)
    ]

    transitions_XY = [z3.And(X == a, Y == b) for a, b in allowed_middle_pairs]
    s.add(z3.Or(transitions_XY))

    transitions_YZ = [z3.And(Y == a, Z == b) for a, b in allowed_middle_pairs]
    s.add(z3.Or(transitions_YZ))

    if s.check() == z3.sat:
        model = s.model()
        X_val = model[X].as_long()
        Y_val = model[Y].as_long()
        Z_val = model[Z].as_long()

        sequence = [0, X_val, Y_val, Z_val, 4]

        start_days = [1]
        end_days = [start_days[0] + durations[cities[0]] - 1]

        for i in range(1, len(sequence)):
            start = end_days[i - 1]
            start_days.append(start)
            city_name = cities[sequence[i]]
            end = start + durations[city_name] - 1
            end_days.append(end)

        itinerary = []
        for i in range(len(sequence)):
            city_name = cities[sequence[i]]
            start = start_days[i]
            end = end_days[i]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city_name})

        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()