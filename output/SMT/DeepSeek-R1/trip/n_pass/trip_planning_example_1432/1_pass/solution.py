from z3 import *

def main():
    cities = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    n_days = 29
    c_index = { 
        "Frankfurt": 0, 
        "Salzburg": 1, 
        "Athens": 2, 
        "Reykjavik": 3, 
        "Bucharest": 4, 
        "Valencia": 5, 
        "Vienna": 6, 
        "Amsterdam": 7, 
        "Stockholm": 8, 
        "Riga": 9 
    }

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
    for (c1, c2) in bidirectional:
        a = c_index[c1]
        b = c_index[c2]
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for (c1, c2) in unidirectional:
        a = c_index[c1]
        b = c_index[c2]
        allowed_flights.add((a, b))

    s = [Int(f's_{i+1}') for i in range(n_days)]
    e = [Int(f'e_{i+1}') for i in range(n_days)]

    solver = Solver()

    for i in range(n_days - 1):
        solver.add(e[i] == s[i+1])
    
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] <= 9)
        solver.add(e[i] >= 0, e[i] <= 9)
    
    flight_conditions = []
    for i in range(n_days):
        flight_possible = []
        for (a, b) in allowed_flights:
            flight_possible.append(And(s[i] == a, e[i] == b))
        solver.add(Implies(s[i] != e[i], Or(flight_possible)))
    
    total_days = [0] * 10
    for c in range(10):
        total = 0
        for i in range(n_days):
            term1 = If(s[i] == c, 1, 0)
            term2 = If(And(e[i] == c, s[i] != c), 1, 0)
            total += term1 + term2
        solver.add(total == [4, 5, 5, 5, 3, 2, 5, 3, 3, 3][c])
    
    for day in range(14, 19):
        i = day - 1
        solver.add(Or(s[i] == 2, e[i] == 2))
    
    for day in [5, 6]:
        i = day - 1
        solver.add(Or(s[i] == 5, e[i] == 5))
    
    vienna_or = []
    for day in range(6, 11):
        i = day - 1
        vienna_or.append(Or(s[i] == 6, e[i] == 6))
    solver.add(Or(vienna_or))
    
    stockholm_or = []
    for day in range(1, 4):
        i = day - 1
        stockholm_or.append(Or(s[i] == 8, e[i] == 8))
    solver.add(Or(stockholm_or))
    
    for day in range(18, 21):
        i = day - 1
        solver.add(Or(s[i] == 9, e[i] == 9))
    
    if solver.check() == sat:
        m = solver.model()
        schedule = []
        for i in range(n_days):
            start_val = m.evaluate(s[i])
            end_val = m.evaluate(e[i])
            start_city = cities[int(str(start_val))]
            end_city = cities[int(str(end_val))]
            if start_val == end_val:
                schedule.append(f"Day {i+1}: Stay in {start_city}")
            else:
                schedule.append(f"Day {i+1}: Fly from {start_city} to {end_city}")
        for sched in schedule:
            print(sched)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()