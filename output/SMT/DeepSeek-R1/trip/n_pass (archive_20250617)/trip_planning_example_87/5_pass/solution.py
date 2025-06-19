from z3 import *

def main():
    s = Solver()
    
    # Cities: 0=Riga, 1=Amsterdam, 2=Mykonos
    city = [Int(f'city_{i}') for i in range(7)]
    travel = [Bool(f'travel_{i}') for i in range(6)]
    
    # Start in Riga on day 1
    s.add(city[0] == 0)
    
    # Cities must be 0, 1, or 2
    for i in range(7):
        s.add(Or(city[i] == 0, city[i] == 1, city[i] == 2))
    
    # Travel constraints: valid connections and same city if not traveling
    for i in range(6):
        s.add(If(travel[i],
                 Or(
                     And(city[i] == 0, city[i+1] == 1),
                     And(city[i] == 1, city[i+1] == 0),
                     And(city[i] == 1, city[i+1] == 2),
                     And(city[i] == 2, city[i+1] == 1)
                 ),
                 city[i] == city[i+1]
                ))
    
    # Must be in Riga on day 1 and day 2
    s.add(If(travel[1],
             Or(city[1] == 0, city[2] == 0),
             city[1] == 0
            ))
    
    # Presence in cities each day
    in_riga = []
    in_amsterdam = []
    in_mykonos = []
    
    # Days 1 to 6 (0-indexed 0 to 5)
    for i in range(6):
        in_riga.append(If(travel[i], Or(city[i] == 0, city[i+1] == 0), city[i] == 0))
        in_amsterdam.append(If(travel[i], Or(city[i] == 1, city[i+1] == 1), city[i] == 1))
        in_mykonos.append(If(travel[i], Or(city[i] == 2, city[i+1] == 2), city[i] == 2))
    
    # Day 7 (0-indexed 6)
    in_riga.append(city[6] == 0)
    in_amsterdam.append(city[6] == 1)
    in_mykonos.append(city[6] == 2)
    
    # Total days per city
    s.add(Sum([If(cond, 1, 0) for cond in in_riga]) == 2)
    s.add(Sum([If(cond, 1, 0) for cond in in_amsterdam]) == 2)
    s.add(Sum([If(cond, 1, 0) for cond in in_mykonos]) == 5)
    
    # Exactly two travel days
    s.add(Sum([If(travel[i], 1, 0) for i in range(6)]) == 2)
    
    # Solve and print
    if s.check() == sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]) for i in range(7)]
        travel_vals = [m.evaluate(travel[i]) for i in range(6)]
        
        names = {0: 'Riga', 1: 'Amsterdam', 2: 'Mykonos'}
        days_output = []
        
        for day in range(7):
            if day < 6 and travel_vals[day]:
                cities = [int(str(city_vals[day])), int(str(city_vals[day+1]))]
            else:
                cities = [int(str(city_vals[day]))]
            city_names = sorted([names[c] for c in set(cities)])
            days_output.append(city_names)
        
        for i, cities in enumerate(days_output, 1):
            print(f"Day {i}: {cities}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()