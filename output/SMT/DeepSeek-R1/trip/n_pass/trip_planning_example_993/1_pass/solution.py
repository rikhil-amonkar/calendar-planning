from z3 import *

def main():
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    dur = {
        "Riga": 2,
        "Frankfurt": 3,
        "Amsterdam": 2,
        "Vilnius": 5,
        "London": 2,
        "Stockholm": 3,
        "Bucharest": 4
    }
    
    connections = [
        ("London", "Amsterdam"),
        ("Vilnius", "Frankfurt"),
        ("Riga", "Vilnius"),
        ("Riga", "Stockholm"),
        ("London", "Bucharest"),
        ("Amsterdam", "Stockholm"),
        ("Amsterdam", "Frankfurt"),
        ("Frankfurt", "Stockholm"),
        ("Bucharest", "Riga"),
        ("Amsterdam", "Riga"),
        ("Amsterdam", "Bucharest"),
        ("Riga", "Frankfurt"),
        ("Bucharest", "Frankfurt"),
        ("London", "Frankfurt"),
        ("London", "Stockholm"),
        ("Amsterdam", "Vilnius")
    ]
    
    s = Solver()
    
    pos = {city: Int(f'pos_{city}') for city in cities}
    
    for city in cities:
        s.add(pos[city] >= 0, pos[city] < 7)
    
    s.add(Distinct([pos[city] for city in cities]))
    
    def is_connected(c1, c2):
        constraints = []
        for a, b in connections:
            constraints.append(And(c1 == a, c2 == b))
            constraints.append(And(c1 == b, c2 == a))
        return Or(constraints)
    
    for k in range(6):
        conds = []
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    conds.append(And(pos[c1] == k, pos[c2] == k + 1, is_connected(c1, c2)))
        s.add(Or(conds))
    
    def start_day(c):
        total = Sum([If(pos[d] < pos[c], dur[d], 0) for d in cities])
        return 1 + total - pos[c]
    
    ams = "Amsterdam"
    vil = "Vilnius"
    stk = "Stockholm"
    
    s_ams = start_day(ams)
    s_vil = start_day(vil)
    s_stk = start_day(stk)
    
    s.add(Or(s_ams == 1, s_ams == 2, s_ams == 3))
    s.add(s_vil >= 3, s_vil <= 11)
    s.add(s_stk >= 11, s_stk <= 13)
    
    if s.check() == sat:
        m = s.model()
        pos_val = {}
        for city in cities:
            pos_val[city] = m.evaluate(pos[city]).as_long()
        
        start_days = {}
        for city in cities:
            start_days[city] = m.evaluate(start_day(city)).as_long()
        
        print("Trip plan:")
        sorted_cities = sorted(cities, key=lambda c: start_days[c])
        for city in sorted_cities:
            start = start_days[city]
            end = start + dur[city] - 1
            print(f"{city}: from day {start} to day {end}")
        
        print("\nDay-by-day schedule:")
        for day in range(1, 16):
            cities_today = []
            for city in cities:
                start = start_days[city]
                end = start + dur[city] - 1
                if start <= day <= end:
                    cities_today.append(city)
            print(f"Day {day}: {', '.join(cities_today)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()