from z3 import *

def main():
    # Cities: H:0, V:1, D:2, P:3, R:4, G:5
    city_names = {
        0: "Helsinki",
        1: "Valencia",
        2: "Dubrovnik",
        3: "Porto",
        4: "Reykjavik",
        5: "Prague"
    }
    # Length of stay for each city
    L = {0:4, 1:5, 2:4, 3:3, 4:4, 5:3}
    edges = [(0,5), (5,1), (1,3), (0,4), (2,0), (4,5)]
    
    # Define variables
    city_at = [Int('city_at_%d' % i) for i in range(6)]
    pos_porto = Int('pos_porto')
    
    s = Solver()
    
    # Each city_at is between 0 and 5 and all are distinct
    for i in range(6):
        s.add(city_at[i] >= 0, city_at[i] <= 5)
    s.add(Distinct(city_at))
    
    # pos_porto is the position of Porto (city 3)
    s.add(Or([And(city_at[k] == 3, pos_porto == k) for k in range(6)]))
    s.add(pos_porto >= 0, pos_porto <= 5)
    
    # Consecutive cities must have a direct flight
    for i in range(5):
        valid = BoolVal(False)
        for (a, b) in edges:
            valid = Or(valid, 
                      And(city_at[i] == a, city_at[i+1] == b),
                      And(city_at[i] == b, city_at[i+1] == a))
        s.add(valid)
    
    # Function to get the length of a city
    def city_length(city):
        return If(city == 0, 4,
              If(city == 1, 5,
              If(city == 2, 4,
              If(city == 3, 3,
              If(city == 4, 4,
              If(city == 5, 3, 0))))))
    
    # Total length of cities before Porto
    total_length_before = 0
    for k in range(6):
        total_length_before += If(k < pos_porto, city_length(city_at[k]), 0)
    
    # Constraint for Porto: 13 <= total_length_before - pos_porto <= 15
    s.add(total_length_before - pos_porto >= 13)
    s.add(total_length_before - pos_porto <= 15)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        city_at_vals = [m.evaluate(city_at[k]).as_long() for k in range(6)]
        pos_porto_val = m.evaluate(pos_porto).as_long()
        
        # Compute start and end days for each segment
        starts = [0] * 6
        ends = [0] * 6
        total = 0
        for k in range(6):
            if k == 0:
                starts[k] = 1
            else:
                starts[k] = 1 + total - k
            city_index = city_at_vals[k]
            length = L[city_index]
            ends[k] = starts[k] + length - 1
            total += length
        
        # Build itinerary
        itinerary = []
        for d in range(1, 19):  # days 1 to 18
            place = None
            for k in range(5, -1, -1):  # check segments in reverse order
                if d >= starts[k] and d <= ends[k]:
                    city_index = city_at_vals[k]
                    place = city_names[city_index]
                    break
            itinerary.append({"day": d, "place": place})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()