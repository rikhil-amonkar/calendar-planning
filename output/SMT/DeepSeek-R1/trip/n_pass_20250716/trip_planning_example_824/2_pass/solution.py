from z3 import *

def main():
    cities = ["Berlin", "Split", "Lyon", "Lisbon", "Bucharest", "Riga", "Tallinn"]
    durations = {
        "Berlin": 5,
        "Split": 3,
        "Lyon": 5,
        "Lisbon": 3,
        "Bucharest": 3,
        "Riga": 5,
        "Tallinn": 4
    }
    sequence = ["Berlin", "Split", "Lyon", "Lisbon", "Bucharest", "Riga", "Tallinn"]
    
    start = {}
    end = {}
    for city in cities:
        start[city] = Int(f'start_{city}')
        end[city] = Int(f'end_{city}')
    
    s = Solver()
    
    s.add(start["Berlin"] == 1)
    s.add(end["Berlin"] == 5)
    s.add(start["Lyon"] == 7)
    s.add(end["Lyon"] == 11)
    s.add(start["Bucharest"] == 13)
    s.add(end["Bucharest"] == 15)
    
    for city in cities:
        s.add(end[city] == start[city] + durations[city] - 1)
    
    for i in range(len(sequence) - 1):
        s.add(end[sequence[i]] == start[sequence[i+1]])
    
    bidirectional_edges = [
        ("Lisbon", "Bucharest"),
        ("Berlin", "Lisbon"),
        ("Bucharest", "Riga"),
        ("Berlin", "Riga"),
        ("Split", "Lyon"),
        ("Lisbon", "Riga"),
        ("Berlin", "Split"),
        ("Lyon", "Lisbon"),
        ("Lyon", "Bucharest"),
        ("Berlin", "Tallinn")
    ]
    directed_edges = [("Riga", "Tallinn")]
    
    allowed_pairs = set()
    for a, b in bidirectional_edges:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    for a, b in directed_edges:
        allowed_pairs.add((a, b))
    
    flight_ok = True
    for i in range(len(sequence) - 1):
        a = sequence[i]
        b = sequence[i+1]
        if (a, b) not in allowed_pairs:
            flight_ok = False
            break
    s.add(flight_ok)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i, city in enumerate(sequence):
            start_val = m.eval(start[city]).as_long()
            end_val = m.eval(end[city]).as_long()
            itinerary.append({"day_range": f"Day {start_val}-{end_val}", "place": city})
            if i < len(sequence) - 1:
                itinerary.append({"day_range": f"Day {end_val}", "place": city})
                next_city = sequence[i+1]
                itinerary.append({"day_range": f"Day {end_val}", "place": next_city})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()