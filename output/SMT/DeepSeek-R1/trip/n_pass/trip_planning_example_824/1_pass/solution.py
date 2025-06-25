from z3 import *

def main():
    cities = ["Berlin", "Split", "Lyon", "Lisbon", "Bucharest", "Riga", "Tallinn"]
    days_req = {
        "Berlin": 5,
        "Split": 3,
        "Lyon": 5,
        "Lisbon": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Tallinn": 4
    }
    start = {}
    end = {}
    for city in cities:
        start[city] = Int(f'start_{city}')
        end[city] = Int(f'end_{city}')

    s = Solver()

    # Fixed constraints
    s.add(start["Berlin"] == 1)
    s.add(end["Berlin"] == 5)
    s.add(start["Lyon"] == 7)
    s.add(end["Lyon"] == 11)
    s.add(start["Bucharest"] == 13)
    s.add(end["Bucharest"] == 15)

    # Duration constraints
    for city in cities:
        s.add(end[city] == start[city] + days_req[city] - 1)

    # Define the sequence of cities
    sequence = ["Berlin", "Split", "Lyon", "Lisbon", "Bucharest", "Riga", "Tallinn"]
    for i in range(len(sequence) - 1):
        s.add(end[sequence[i]] == start[sequence[i+1]])

    # Flight constraints (allowed pairs)
    bidirectional_edges = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Berlin", "Tallinn"),
        ("Lyon", "Bucharest")
    ]
    directed_edges = [("Riga", "Tallinn")]
    allowed_pairs = set()
    for a, b in bidirectional_edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    for a, b in directed_edges:
        allowed_pairs.add((a, b))

    for i in range(len(sequence) - 1):
        a, b = sequence[i], sequence[i+1]
        s.add(Or(*[And(a == pair[0], b == pair[1]) for pair in allowed_pairs if pair[0] == a and pair[1] == b))

    # Bounds for start and end days
    for city in cities:
        s.add(start[city] >= 1)
        s.add(start[city] <= 22)
        s.add(end[city] >= 1)
        s.add(end[city] <= 22)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i, city in enumerate(sequence):
            s_val = m.eval(start[city]).as_long()
            e_val = m.eval(end[city]).as_long()
            itinerary.append({"day_range": f"Day {s_val}-{e_val}", "place": city})
            if i < len(sequence) - 1:
                flight_day = e_val
                itinerary.append({"day_range": f"Day {flight_day}", "place": city})
                next_city = sequence[i+1]
                itinerary.append({"day_range": f"Day {flight_day}", "place": next_city})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()