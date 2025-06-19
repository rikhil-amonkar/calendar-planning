from z3 import *

def main():
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    n_days = 29
    c_index = {city: i for i, city in enumerate(cities)}
    
    # Define allowed flights
    bidirectional = [
        ("Valencia", "Frankfurt"), ("Vienna", "Bucharest"), ("Athens", "Bucharest"),
        ("Riga", "Frankfurt"), ("Stockholm", "Athens"), ("Amsterdam", "Bucharest"),
        ("Amsterdam", "Frankfurt"), ("Stockholm", "Vienna"), ("Vienna", "Riga"),
        ("Amsterdam", "Reykjavik"), ("Reykjavik", "Frankfurt"), ("Stockholm", "Amsterdam"),
        ("Amsterdam", "Valencia"), ("Vienna", "Frankfurt"), ("Valencia", "Bucharest"),
        ("Bucharest", "Frankfurt"), ("Stockholm", "Frankfurt"), ("Valencia", "Vienna"),
        ("Frankfurt", "Salzburg"), ("Amsterdam", "Vienna"), ("Stockholm", "Reykjavik"),
        ("Amsterdam", "Riga"), ("Stockholm", "Riga"), ("Vienna", "Reykjavik"),
        ("Amsterdam", "Athens"), ("Athens", "Frankfurt"), ("Vienna", "Athens"), ("Riga", "Bucharest")
    ]
    unidirectional = [("Valencia", "Athens"), ("Athens", "Riga"), ("Reykjavik", "Athens")]
    
    # Create allowed flight pairs
    allowed_pairs = []
    for (c1, c2) in bidirectional:
        i1, i2 = c_index[c1], c_index[c2]
        allowed_pairs.append((i1, i2))
        allowed_pairs.append((i2, i1))
    for (c1, c2) in unidirectional:
        i1, i2 = c_index[c1], c_index[c2]
        allowed_pairs.append((i1, i2))
    
    # Create solver and city variables
    s = Solver()
    c = [Int(f"c_{i}") for i in range(n_days)]
    
    # City domain constraint
    for i in range(n_days):
        s.add(c[i] >= 0, c[i] < len(cities))
    
    # Flight constraints
    for i in range(n_days - 1):
        current = c[i]
        next_c = c[i + 1]
        s.add(Or(
            current == next_c,  # Stay in same city
            Or([And(current == a, next_c == b) for (a, b) in allowed_pairs])  # Valid flight
        ))
    
    # Stay duration constraints
    durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]  # Frankfurt to Riga
    for city_idx, days in enumerate(durations):
        s.add(Sum([If(c[i] == city_idx, 1, 0) for i in range(n_days)]) == days)
    
    # Event constraints
    s.add(Or(c[4] == c_index["Valencia"], c[5] == c_index["Valencia"]))  # Valencia show (day 5-6)
    s.add(Or([c[i] == c_index["Athens"] for i in range(13, 18)]))  # Athens workshop (day 14-18)
    s.add(Or([c[i] == c_index["Vienna"] for i in range(5, 10)]))  # Vienna wedding (day 6-10)
    s.add(Or([c[i] == c_index["Stockholm"] for i in range(0, 3)]))  # Stockholm meeting (day 1-3)
    s.add(Or([c[i] == c_index["Riga"] for i in range(17, 20)]))  # Riga conference (day 18-20)
    
    # Additional constraint: Valencia must be visited on both days 5 and 6
    s.add(c[4] == c_index["Valencia"])
    s.add(c[5] == c_index["Valencia"])
    
    # Solve and print itinerary
    if s.check() == sat:
        m = s.model()
        schedule = []
        prev_city = None
        for day in range(n_days):
            city_idx = m.evaluate(c[day]).as_long()
            city = cities[city_idx]
            if day == 0:
                schedule.append(f"Day 1: Arrive in {city}")
            elif city_idx == prev_city:
                schedule.append(f"Day {day + 1}: Stay in {city}")
            else:
                schedule.append(f"Day {day + 1}: Fly from {cities[prev_city]} to {city}")
            prev_city = city_idx
        for entry in schedule:
            print(entry)
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()