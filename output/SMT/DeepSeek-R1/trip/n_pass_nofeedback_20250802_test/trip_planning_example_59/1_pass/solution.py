import z3
import json

def main():
    # Create Z3 variables for the stay city for each day (1 to 16)
    stay = [z3.Int(f'stay_{d}') for d in range(1, 17)]
    
    s = z3.Solver()
    
    # Each stay variable must be 0 (Bucharest), 1 (Lyon), or 2 (Porto)
    for i in range(16):
        s.add(z3.Or(stay[i] == 0, stay[i] == 1, stay[i] == 2))
    
    # Flight constraints: if the city changes between consecutive days, the pair must have a direct flight
    for i in range(1, 16):
        prev_city = stay[i-1]
        curr_city = stay[i]
        s.add(z3.Implies(prev_city != curr_city,
                         z3.Or(z3.And(prev_city == 0, curr_city == 1),
                               z3.And(prev_city == 1, curr_city == 0),
                               z3.And(prev_city == 1, curr_city == 2),
                               z3.And(prev_city == 2, curr_city == 1))
                         ))
    
    # Function to determine presence in a city on a given day
    def presence(city, day_index):
        if day_index == 0:
            return stay[0] == city
        else:
            return z3.Or(stay[day_index] == city, 
                         z3.And(stay[day_index-1] == city, stay[day_index] != city))
    
    # Total days in each city
    total_bucharest = z3.Sum([z3.If(presence(0, i), 1, 0) for i in range(16)])
    total_lyon = z3.Sum([z3.If(presence(1, i), 1, 0) for i in range(16)])
    total_porto = z3.Sum([z3.If(presence(2, i), 1, 0) for i in range(16)])
    
    s.add(total_bucharest == 7)
    s.add(total_lyon == 7)
    s.add(total_porto == 4)
    
    # Wedding constraint: must be in Bucharest on at least one day between 1 and 7
    s.add(z3.Or([presence(0, i) for i in range(7)]))  # Days 1 to 7 (indices 0 to 6)
    
    # Check if a solution exists
    if s.check() == z3.sat:
        m = s.model()
        itinerary_list = []
        city_names = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
        for i in range(16):
            city_val = m[stay[i]].as_long()
            itinerary_list.append({"day": i+1, "city": city_names[city_val]})
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()