from z3 import *

def main():
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    n_days = 29
    c_index = {city: idx for idx, city in enumerate(cities)}
    
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
    
    allowed_flights = set()
    for c1, c2 in bidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_flights.add((idx1, idx2))
        allowed_flights.add((idx2, idx1))
    for c1, c2 in unidirectional:
        idx1, idx2 = c_index[c1], c_index[c2]
        allowed_flights.add((idx1, idx2))
    
    s = [Int(f's_{i}') for i in range(n_days)]
    e = [Int(f'e_{i}') for i in range(n_days)]
    
    solver = Solver()
    
    for i in range(n_days - 1):
        solver.add(e[i] == s[i + 1])
    
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] < 10)
        solver.add(e[i] >= 0, e[i] < 10)
    
    for i in range(n_days):
        flight_possible = []
        for flight in allowed_flights:
            flight_possible.append(And(s[i] == flight[0], e[i] == flight[1]))
        solver.add(Implies(s[i] != e[i], Or(flight_possible)))
    
    stay_durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    for city_idx, duration in enumerate(stay_durations):
        total_days = 0
        for day in range(n_days):
            total_days += If(Or(s[day] == city_idx, And(e[day] == city_idx, s[day] != city_idx)), 1, 0)
        solver.add(total_days == duration)
    
    # Athens workshop: at least one day between 14-18
    athens_days = []
    for day in range(13, 18):
        athens_days.append(Or(s[day] == c_index["Athens"], e[day] == c_index["Athens"]))
    solver.add(Or(athens_days))
    
    # Valencia show: both days 5 and 6
    solver.add(Or(s[4] == c_index["Valencia"], e[4] == c_index["Valencia"]))
    solver.add(Or(s[5] == c_index["Valencia"], e[5] == c_index["Valencia"]))
    
    # Vienna wedding: at least one day between 6-10
    vienna_days = []
    for day in range(5, 10):
        vienna_days.append(Or(s[day] == c_index["Vienna"], e[day] == c_index["Vienna"]))
    solver.add(Or(vienna_days))
    
    # Stockholm meeting: at least one day between 1-3
    stockholm_days = []
    for day in range(0, 3):
        stockholm_days.append(Or(s[day] == c_index["Stockholm"], e[day] == c_index["Stockholm"]))
    solver.add(Or(stockholm_days))
    
    # Riga conference: at least one day between 18-20
    riga_days = []
    for day in range(17, 20):
        riga_days.append(Or(s[day] == c_index["Riga"], e[day] == c_index["Riga"]))
    solver.add(Or(riga_days))
    
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