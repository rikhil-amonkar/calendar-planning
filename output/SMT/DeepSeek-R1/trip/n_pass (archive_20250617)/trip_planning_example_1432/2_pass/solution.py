from z3 import *

def main():
    # Define cities and map to indices
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    n_days = 29
    c_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define allowed flights (bidirectional and unidirectional)
    bidirectional = [
        ("Valencia", "Frankfurt"),
        ("Vienna", "Bucharest"),
        ("Athens", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Stockholm", "Athens"),
        ("Amsterdam", "Bucharest"),
        ("Amsterdam", "Frankfurt"),
        ("Stockholm", "Vienna"),
        ("Vienna", "Riga"),
        ("Amsterdam", "Reykjavik"),
        ("Reykjavik", "Frankfurt"),
        ("Stockholm", "Amsterdam"),
        ("Amsterdam", "Valencia"),
        ("Vienna", "Frankfurt"),
        ("Valencia", "Bucharest"),
        ("Bucharest", "Frankfurt"),
        ("Stockholm", "Frankfurt"),
        ("Valencia", "Vienna"),
        ("Frankfurt", "Salzburg"),
        ("Amsterdam", "Vienna"),
        ("Stockholm", "Reykjavik"),
        ("Amsterdam", "Riga"),
        ("Stockholm", "Riga"),
        ("Vienna", "Reykjavik"),
        ("Amsterdam", "Athens"),
        ("Athens", "Frankfurt"),
        ("Vienna", "Athens"),
        ("Riga", "Bucharest")
    ]
    
    unidirectional = [
        ("Valencia", "Athens"),
        ("Athens", "Riga"),
        ("Reykjavik", "Athens")
    ]
    
    # Create set of allowed flights (both directions for bidirectional, single direction for unidirectional)
    allowed_flights = set()
    for c1, c2 in bidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_flights.add((idx1, idx2))
        allowed_flights.add((idx2, idx1))
    for c1, c2 in unidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_flights.add((idx1, idx2))
    
    # Create start and end city variables for each day
    s = [Int(f's_{i}') for i in range(n_days)]
    e = [Int(f'e_{i}') for i in range(n_days)]
    
    solver = Solver()
    
    # Continuity constraint: end city of day i must match start city of day i+1
    for i in range(n_days - 1):
        solver.add(e[i] == s[i + 1])
    
    # Each city variable must be between 0 and 9 (inclusive)
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] < 10)
        solver.add(e[i] >= 0, e[i] < 10)
    
    # Flight constraints: if start and end cities differ, the flight must be allowed
    for i in range(n_days):
        flight_possible = []
        for flight in allowed_flights:
            solver.add(Implies(And(s[i] == flight[0], e[i] == flight[1]), True))
            flight_possible.append(And(s[i] == flight[0], e[i] == flight[1]))
        solver.add(Implies(s[i] != e[i], Or(flight_possible)))
    
    # Stay duration constraints
    stay_durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]  # Frankfurt, Salzburg, ..., Riga
    for city_idx, duration in enumerate(stay_durations):
        total_days = 0
        for day in range(n_days):
            # Count day if: start in city OR (end in city AND didn't start in city)
            total_days += If(Or(s[day] == city_idx, And(e[day] == city_idx, s[day] != city_idx)), 1, 0)
        solver.add(total_days == duration)
    
    # Event attendance constraints
    # Athens workshop between day 14-18 (inclusive)
    for day in range(13, 18):  # Days 14 to 18 (0-indexed: 13 to 17)
        solver.add(Or(s[day] == c_index["Athens"], e[day] == c_index["Athens"]))
    
    # Valencia show on day 5 and 6
    for day in [4, 5]:  # Days 5 and 6
        solver.add(Or(s[day] == c_index["Valencia"], e[day] == c_index["Valencia"]))
    
    # Vienna wedding between day 6-10 (inclusive)
    for day in range(5, 10):  # Days 6 to 10
        solver.add(Or(s[day] == c_index["Vienna"], e[day] == c_index["Vienna"]))
    
    # Stockholm meeting between day 1-3 (inclusive)
    for day in range(0, 3):  # Days 1 to 3
        solver.add(Or(s[day] == c_index["Stockholm"], e[day] == c_index["Stockholm"]))
    
    # Riga conference between day 18-20 (inclusive)
    for day in range(17, 20):  # Days 18 to 20
        solver.add(Or(s[day] == c_index["Riga"], e[day] == c_index["Riga"]))
    
    # Check for a valid solution
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        for day in range(n_days):
            start_city = cities[model.evaluate(s[day]).as_long()]
            end_city = cities[model.evaluate(e[day]).as_long()]
            if start_city == end_city:
                schedule.append(f"Day {day + 1}: Stay in {start_city}")
            else:
                schedule.append(f"Day {day + 1}: Fly from {start_city} to {end_city}")
        for entry in schedule:
            print(entry)
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()