from z3 import *

def main():
    s = Solver()
    
    # Cities: 0=Riga, 1=Amsterdam, 2=Mykonos
    city = [Int(f'city_{i+1}') for i in range(7)]
    travel = [Bool(f'travel_{i+1}') for i in range(6)]
    
    # Constraint: Start in Riga on day 1
    s.add(city[0] == 0)
    
    # All cities must be 0, 1, or 2
    for c in city:
        s.add(Or(c == 0, c == 1, c == 2))
    
    # Travel constraints for days 1 to 6
    for i in range(6):
        s.add(If(travel[i],
                 And(
                     city[i] != city[i+1],
                     Or(
                         And(city[i] == 0, city[i+1] == 1),
                         And(city[i] == 1, city[i+1] == 0),
                         And(city[i] == 1, city[i+1] == 2),
                         And(city[i] == 2, city[i+1] == 1)
                     )
                 ),
                 city[i+1] == city[i]
                ))
    
    # Presence in cities for each day
    in_riga = []
    in_amsterdam = []
    in_mykonos = []
    
    # Days 1 to 6
    for i in range(6):
        in_riga.append(Or(city[i] == 0, And(travel[i], city[i+1] == 0)))
        in_amsterdam.append(Or(city[i] == 1, And(travel[i], city[i+1] == 1)))
        in_mykonos.append(Or(city[i] == 2, And(travel[i], city[i+1] == 2)))
    
    # Day 7
    in_riga.append(city[6] == 0)
    in_amsterdam.append(city[6] == 1)
    in_mykonos.append(city[6] == 2)
    
    # Must be in Riga on days 1 and 2
    s.add(in_riga[0])
    s.add(in_riga[1])
    
    # Total days in each city
    s.add(Sum([If(b, 1, 0) for b in in_riga]) == 2)
    s.add(Sum([If(b, 1, 0) for b in in_amsterdam]) == 2)
    s.add(Sum([If(b, 1, 0) for b in in_mykonos]) == 5)
    
    # Exactly 2 travel days
    s.add(Sum([If(t, 1, 0) for t in travel]) == 2)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        city_vals = [m.eval(city[i]) for i in range(7)]
        travel_vals = [m.eval(travel[i]) for i in range(6)]
        
        names = {0: 'Riga', 1: 'Amsterdam', 2: 'Mykonos'}
        
        for day in range(7):
            cities_set = set()
            cities_set.add(int(str(city_vals[day])))
            if day < 6 and travel_vals[day]:
                cities_set.add(int(str(city_vals[day+1])))
            city_names = sorted([names[c] for c in cities_set])
            print(f"Day {day+1}: {city_names}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()