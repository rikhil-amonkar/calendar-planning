from z3 import *
import json

def main():
    # Define the city mapping
    cities = ["Barcelona", "Oslo", "Stuttgart", "Venice", "Split", "Brussels", "Copenhagen"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    
    # Define direct flights as a set of tuples (sorted)
    flight_pairs = [
        ("Venice", "Stuttgart"),
        ("Oslo", "Brussels"),
        ("Split", "Copenhagen"),
        ("Barcelona", "Copenhagen"),
        ("Barcelona", "Venice"),
        ("Brussels", "Venice"),
        ("Barcelona", "Stuttgart"),
        ("Copenhagen", "Brussels"),
        ("Oslo", "Split"),
        ("Oslo", "Venice"),
        ("Barcelona", "Split"),
        ("Oslo", "Copenhagen"),
        ("Barcelona", "Oslo"),
        ("Copenhagen", "Stuttgart"),
        ("Split", "Stuttgart"),
        ("Copenhagen", "Venice"),
        ("Barcelona", "Brussels")
    ]
    flights_set = set()
    for a, b in flight_pairs:
        int_a = city_to_int[a]
        int_b = city_to_int[b]
        flights_set.add((int_a, int_b))
    
    # Define variables
    e2 = Int('e2')
    e3 = Int('e3')
    e4 = Int('e4')
    e5 = Int('e5')
    e6 = Int('e6')
    
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    s5 = Int('s5')
    s6 = Int('s6')
    s7 = Int('s7')
    
    s = [0, s2, s3, s4, s5, s6, s7]  # s0 is Barcelona (0)
    ends = [3, e2, e3, e4, e5, e6, 16]  # ends[0] is end of segment0 (Barcelona) = 3, segment7 ends at 16.
    starts = [1, 3, e2, e3, e4, e5, e6]  # starts[0]=1, starts[1]=3, starts[2]=e2, ... starts[6]=e6.
    
    solver = Solver()
    
    # Constraints for end days: increasing and within [3,16]
    solver.add(e2 >= 3, e2 <= 16)
    solver.add(e3 >= e2, e3 <= 16)
    solver.add(e4 >= e3, e4 <= 16)
    solver.add(e5 >= e4, e5 <= 16)
    solver.add(e6 >= e5, e6 <= 16)
    
    # Constraints for city assignments: distinct and in 1..6
    solver.add(Distinct(s2, s3, s4, s5, s6, s7))
    for x in [s2, s3, s4, s5, s6, s7]:
        solver.add(x >= 1, x <= 6)
    
    # Duration constraints for segments 1 to 6 (index1 to 6 in s, which are segments1 to 6)
    for i in range(1, 7):  # i from 1 to 6: segments1 to 6
        # duration = ends[i] - starts[i] + 1 = ends[i] - ends[i-1] + 1
        # And we set it to the required days for the city s[i]
        solver.add(
            If(s[i] == 1, ends[i] == ends[i-1] + 1,  # Oslo: 2 days -> duration=2 -> ends[i] = ends[i-1] + 1
            If(s[i] == 2, ends[i] == ends[i-1] + 2,  # Stuttgart: 3 days -> ends[i] = ends[i-1] + 2
            If(s[i] == 3, ends[i] == ends[i-1] + 3,  # Venice: 4 days -> ends[i] = ends[i-1] + 3
            If(s[i] == 4, ends[i] == ends[i-1] + 3,  # Split: 4 days
            If(s[i] == 5, ends[i] == ends[i-1] + 2,  # Brussels: 3 days
            If(s[i] == 6, ends[i] == ends[i-1] + 2,  # Copenhagen: 3 days
            BoolVal(False))))))
        )
    
    # Duration constraint for segment7 (index6 in s, which is the last segment)
    # duration = 16 - starts[6] + 1 = 17 - starts[6] = 17 - e6 (since starts[6]=e6)
    solver.add(
        If(s[6] == 1, 17 - e6 == 2,  # Oslo: 2 days -> e6=15
        If(s[6] == 2, 17 - e6 == 3,   # Stuttgart: 3 days -> e6=14
        If(s[6] == 3, 17 - e6 == 4,   # Venice: 4 days -> e6=13
        If(s[6] == 4, 17 - e6 == 4,   # Split: 4 days -> e6=13
        If(s[6] == 5, 17 - e6 == 3,   # Brussels: 3 days -> e6=14
        If(s[6] == 6, 17 - e6 == 3,   # Copenhagen: 3 days -> e6=14
        BoolVal(False))))))
    )
    
    # Meeting constraints for Oslo and Brussels (for segments1 to 6, i.e., i=1 to 6 in s)
    for i in range(1, 7):  # i=1 to 6: segments1 to 6 (second to seventh)
        # For Oslo (city1): if segment i is Oslo, then starts[i] <=4 -> starts[i] = ends[i-1] <=4
        solver.add(If(s[i] == 1, ends[i-1] <= 4, True))
        # For Brussels (city5): if segment i is Brussels, then starts[i] <=11 and ends[i] >=9
        solver.add(If(s[i] == 5, And(ends[i-1] <= 11, ends[i] >= 9), True))
    
    # Meeting constraints for the last segment (segment7, i=6 in s)
    # For Oslo: if segment7 is Oslo, then starts[6] <=4 -> starts[6]=e5 <=4
    solver.add(If(s[6] == 1, e5 <= 4, True))
    # For Brussels: if segment7 is Brussels, then starts[6] <=11 -> e5<=11 (and ends[6]=16>=9, always true)
    solver.add(If(s[6] == 5, e5 <= 11, True))
    
    # Flight connections between consecutive segments
    for i in range(6):  # i from 0 to 5: pairs (s[i], s[i+1])
        c1 = s[i]
        c2 = s[i+1]
        conds = []
        for (a, b) in flights_set:
            conds.append(And(c1 == a, c2 == b))
            conds.append(And(c1 == b, c2 == a))
        solver.add(Or(conds))
    
    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        # Extract the values for the city assignments and end days
        s_val = [0]  # segment0 is Barcelona
        s_val.append(model.evaluate(s2).as_long())
        s_val.append(model.evaluate(s3).as_long())
        s_val.append(model.evaluate(s4).as_long())
        s_val.append(model.evaluate(s5).as_long())
        s_val.append(model.evaluate(s6).as_long())
        s_val.append(model.evaluate(s7).as_long())
        
        ends_val = [3]  # end of segment0
        ends_val.append(model.evaluate(e2).as_long())
        ends_val.append(model.evaluate(e3).as_long())
        ends_val.append(model.evaluate(e4).as_long())
        ends_val.append(model.evaluate(e5).as_long())
        ends_val.append(model.evaluate(e6).as_long())
        ends_val.append(16)  # end of segment7
        
        starts_val = [1]  # start of segment0
        for i in range(1, 7):
            starts_val.append(ends_val[i-1])  # start of segment i = end of segment i-1
        
        # Build the itinerary
        itinerary = []
        for i in range(7):  # for each segment
            start = starts_val[i]
            end = ends_val[i]
            city_name = cities[s_val[i]]
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
            if i < 6:  # not the last segment: add flight day records
                departure_city = cities[s_val[i]]
                arrival_city = cities[s_val[i+1]]
                itinerary.append({"day_range": f"Day {end}", "place": departure_city})
                itinerary.append({"day_range": f"Day {end}", "place": arrival_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()