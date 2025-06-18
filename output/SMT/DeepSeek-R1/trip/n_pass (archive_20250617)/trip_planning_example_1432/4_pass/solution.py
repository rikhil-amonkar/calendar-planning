from z3 import *

def main():
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
    
    # Create set of allowed flight pairs
    allowed_pairs = set()
    for c1, c2 in bidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_pairs.add((idx1, idx2))
        allowed_pairs.add((idx2, idx1))
    for c1, c2 in unidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_pairs.add((idx1, idx2))
    
    # City variables for each day
    c = [Int(f'c_{i}') for i in range(n_days)]
    solver = Solver()
    
    # Each day must be a valid city index
    for i in range(n_days):
        solver.add(c[i] >= 0, c[i] < len(cities))
    
    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        same_city = c[i] == c[i + 1]
        valid_flight = Or([And(c[i] == a, c[i + 1] == b) for (a, b) in allowed_pairs])
        solver.add(Or(same_city, valid_flight))
    
    # Stay duration constraints
    stay_durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]  # Frankfurt, Salzburg, ..., Riga
    for city_idx, duration in enumerate(stay_durations):
        solver.add(Sum([If(c[i] == city_idx, 1, 0) for i in range(n_days)]) == duration)
    
    # Event attendance constraints
    athens_idx = c_index["Athens"]
    valencia_idx = c_index["Valencia"]
    vienna_idx = c_index["Vienna"]
    stockholm_idx = c_index["Stockholm"]
    riga_idx = c_index["Riga"]
    
    # Athens workshop: at least one day between 14-18
    solver.add(Or([c[i] == athens_idx for i in range(13, 18)]))
    
    # Valencia show: both days 5 and 6
    solver.add(c[4] == valencia_idx)
    solver.add(c[5] == valencia_idx)
    
    # Vienna wedding: at least one day between 6-10
    solver.add(Or([c[i] == vienna_idx for i in range(5, 10)]))
    
    # Stockholm meeting: at least one day between 1-3
    solver.add(Or([c[i] == stockholm_idx for i in range(0, 3)]))
    
    # Riga conference: at least one day between 18-20
    solver.add(Or([c[i] == riga_idx for i in range(17, 20)]))
    
    # Solve and print itinerary
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        for day in range(n_days):
            city_idx = model.evaluate(c[day]).as_long()
            city = cities[city_idx]
            if day == 0 or city_idx != model.evaluate(c[day-1]).as_long():
                schedule.append(f"Day {day + 1}: Arrive in {city}")
            else:
                schedule.append(f"Day {day + 1}: Stay in {city}")
        for entry in schedule:
            print(entry)
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()