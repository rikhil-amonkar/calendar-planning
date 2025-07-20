from z3 import *

def main():
    s0, s1, s2, s3 = Ints('s0 s1 s2 s3')
    t1, t2, t3 = Ints('t1 t2 t3')
    
    solver = Solver()
    
    # Constraints: t1, t2, t3 are between 1 and 14 and ordered
    solver.add(t1 >= 1, t1 <= 14)
    solver.add(t2 >= 1, t2 <= 14)
    solver.add(t3 >= 1, t3 <= 14)
    solver.add(t1 < t2, t2 < t3)
    
    # Cities are distinct and each between 0 and 3 (Vienna=0, Lyon=1, Amsterdam=2, Santorini=3)
    solver.add(Distinct(s0, s1, s2, s3))
    solver.add(s0 >= 0, s0 <= 3)
    solver.add(s1 >= 0, s1 <= 3)
    solver.add(s2 >= 0, s2 <= 3)
    solver.add(s3 >= 0, s3 <= 3)
    
    # Days in each city
    def days_in_city(city):
        return If(s0 == city, t1,
               If(s1 == city, t2 - t1 + 1,
               If(s2 == city, t3 - t2 + 1,
               If(s3 == city, 14 - t3 + 1, 0))))
    
    solver.add(days_in_city(0) == 7)  # Vienna
    solver.add(days_in_city(1) == 3)  # Lyon
    solver.add(days_in_city(2) == 3)  # Amsterdam
    solver.add(days_in_city(3) == 4)  # Santorini
    
    # Event constraints: Lyon must be present on days 7,8,9 and Amsterdam on days 9,10,11
    for d in [7, 8, 9]:
        in_lyon = Or(
            And(s0 == 1, d <= t1),        # Lyon is the first city
            And(s1 == 1, And(d >= t1, d <= t2)), # Lyon is the second city
            And(s2 == 1, And(d >= t2, d <= t3)), # Lyon is the third city
            And(s3 == 1, d >= t3)         # Lyon is the last city
        )
        solver.add(in_lyon)
    
    for d in [9, 10, 11]:
        in_amsterdam = Or(
            And(s0 == 2, d <= t1),        # Amsterdam is the first city
            And(s1 == 2, And(d >= t1, d <= t2)), # Amsterdam is the second city
            And(s2 == 2, And(d >= t2, d <= t3)), # Amsterdam is the third city
            And(s3 == 2, d >= t3)         # Amsterdam is the last city
        )
        solver.add(in_amsterdam)
    
    # Flight connections: define the direct flight pairs (both directions)
    connections = [
        (0, 1), (1, 0),  # Vienna <-> Lyon
        (0, 3), (3, 0),  # Vienna <-> Santorini
        (0, 2), (2, 0),  # Vienna <-> Amsterdam
        (2, 3), (3, 2),  # Amsterdam <-> Santorini
        (1, 2), (2, 1)   # Lyon <-> Amsterdam
    ]
    
    # Constraint for consecutive cities being connected
    def connected(city1, city2):
        options = []
        for a, b in connections:
            options.append(And(city1 == a, city2 == b))
        return Or(options)
    
    solver.add(connected(s0, s1))
    solver.add(connected(s1, s2))
    solver.add(connected(s2, s3))
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        s0_val = model[s0].as_long()
        s1_val = model[s1].as_long()
        s2_val = model[s2].as_long()
        s3_val = model[s3].as_long()
        t1_val = model[t1].as_long()
        t2_val = model[t2].as_long()
        t3_val = model[t3].as_long()
        
        city_names = {
            0: "Vienna",
            1: "Lyon",
            2: "Amsterdam",
            3: "Santorini"
        }
        
        name0 = city_names[s0_val]
        name1 = city_names[s1_val]
        name2 = city_names[s2_val]
        name3 = city_names[s3_val]
        
        # Build the itinerary
        itinerary = [
            {"day_range": "Day 1-{}".format(t1_val), "place": name0},
            {"day_range": "Day {}".format(t1_val), "place": name0},
            {"day_range": "Day {}".format(t1_val), "place": name1},
            {"day_range": "Day {}-{}".format(t1_val, t2_val), "place": name1},
            {"day_range": "Day {}".format(t2_val), "place": name1},
            {"day_range": "Day {}".format(t2_val), "place": name2},
            {"day_range": "Day {}-{}".format(t2_val, t3_val), "place": name2},
            {"day_range": "Day {}".format(t3_val), "place": name2},
            {"day_range": "Day {}".format(t3_val), "place": name3},
            {"day_range": "Day {}-14".format(t3_val), "place": name3}
        ]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()