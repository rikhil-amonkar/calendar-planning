from z3 import *

def main():
    s = [Int(f's_{i}') for i in range(12)]
    solver = Solver()
    
    # Each s_i must be 0, 1, or 2
    for i in range(12):
        solver.add(s[i] >= 0, s[i] <= 2)
    
    # Transition constraints
    for i in range(11):
        # If current is Dublin (0), next can be Dublin (0) or Riga (1)
        solver.add(Implies(s[i] == 0, Or(s[i+1] == 0, s[i+1] == 1)))
        # If current is Riga (1), next can be Dublin (0), Riga (1), or Vilnius (2)
        solver.add(Implies(s[i] == 1, Or(s[i+1] == 0, s[i+1] == 1, s[i+1] == 2)))
        # If current is Vilnius (2), next must be Vilnius (2)
        solver.add(Implies(s[i] == 2, s[i+1] == 2))
    
    # Count for Dublin (0)
    count0 = If(s[0] == 0, 1, 0)
    for i in range(11):
        count0 += If(Or(s[i] == 0, s[i+1] == 0), 1, 0)
    
    # Count for Riga (1)
    count1 = If(s[0] == 1, 1, 0)
    for i in range(11):
        count1 += If(Or(s[i] == 1, s[i+1] == 1), 1, 0)
    
    # Count for Vilnius (2)
    count2 = If(s[0] == 2, 1, 0)
    for i in range(11):
        count2 += If(Or(s[i] == 2, s[i+1] == 2), 1, 0)
    
    solver.add(count0 == 2)
    solver.add(count1 == 5)
    solver.add(count2 == 7)
    
    if solver.check() == sat:
        model = solver.model()
        sleep_vals = [model.evaluate(s[i]) for i in range(12)]
        itinerary = []
        city_map = {0: 'Dublin', 1: 'Riga', 2: 'Vilnius'}
        for i in range(12):
            day = i + 1
            city_index = sleep_vals[i].as_long()
            city_name = city_map[city_index]
            itinerary.append({'day': day, 'city': city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()