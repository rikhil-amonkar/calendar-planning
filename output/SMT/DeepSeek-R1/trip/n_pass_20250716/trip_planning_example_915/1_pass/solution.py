from z3 import *
import json

def main():
    # Define the cities by number
    Bucharest = 0
    Venice = 1
    Prague = 2
    Frankfurt = 3
    Zurich = 4
    Florence = 5
    Tallinn = 6

    cities = [Bucharest, Venice, Prague, Frankfurt, Zurich, Florence, Tallinn]
    city_names = {
        Bucharest: "Bucharest",
        Venice: "Venice",
        Prague: "Prague",
        Frankfurt: "Frankfurt",
        Zurich: "Zurich",
        Florence: "Florence",
        Tallinn: "Tallinn"
    }
    
    # Directed edges: set of (from, to)
    edges = {
        (2,6), (6,2),
        (2,4), (4,2),
        (5,2), (2,5),
        (3,0), (0,3),
        (3,1), (1,3),
        (2,0), (0,2),
        (0,4), (4,0),
        (6,3), (3,6),
        (4,5)   # Zurich->Florence
    }
    
    # Create solver
    s = Solver()
    
    # Sequence of cities: s0 to s6
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    s5 = Int('s5')
    s6 = Int('s6')
    seq = [s0, s1, s2, s3, s4, s5, s6]
    
    # Flight days: d1 to d6
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    d4 = Int('d4')
    d5 = Int('d5')
    d6 = Int('d6')
    days = [d1, d2, d3, d4, d5, d6]
    
    # Each element in seq is between 0 and 6
    for i in range(7):
        s.add(seq[i] >= 0, seq[i] <= 6)
    
    # Distinct
    s.add(Distinct(seq))
    
    # Flight day order: 1<=d1<d2<...<d6<=26
    s.add(d1>=1, d1<=26)
    for i in range(5):
        s.add(days[i] < days[i+1])
    s.add(d6<=26)
    
    # Flight edges: for each consecutive pair in the sequence, (seq[i], seq[i+1]) must be in edges
    for i in range(6):
        edge_constraints = []
        for (a,b) in edges:
            edge_constraints.append(And(seq[i]==a, seq[i+1]==b))
        s.add(Or(edge_constraints))
    
    # Required days for each city
    required_days = {
        Bucharest: 3,
        Venice: 5,
        Prague: 4,
        Frankfurt: 5,
        Zurich: 5,
        Florence: 5,
        Tallinn: 5
    }
    
    for j in cities:
        stay_j = If(seq[0] == j, d1,
                If(seq[1] == j, d2 - d1 + 1,
                If(seq[2] == j, d3 - d2 + 1,
                If(seq[3] == j, d4 - d3 + 1,
                If(seq[4] == j, d5 - d4 + 1,
                If(seq[5] == j, d6 - d5 + 1,
                If(seq[6] == j, 26 - d6 + 1, 0)))))))
        s.add(stay_j == required_days[j])
    
    # Event constraints:
    # Venice: if first city, then d1>=22; if middle, then d_{i+1}>=22; if last, no constraint.
    for i in range(7):
        if i == 0:
            s.add(Implies(seq[0] == Venice, d1 >= 22))
        elif i == 6:
            pass
        else:
            s.add(Implies(seq[i] == Venice, days[i] >= 22))
    
    # Frankfurt: 
    for i in range(7):
        if i == 0:
            s.add(Implies(seq[0] == Frankfurt, d1 >= 12))
        elif i == 6:
            s.add(Implies(seq[6] == Frankfurt, d6 <= 16))
        else:
            s.add(Implies(seq[i] == Frankfurt, And(days[i-1] <= 16, days[i] >= 12)))
    
    # Tallinn: 
    for i in range(7):
        if i == 0:
            s.add(Implies(seq[0] == Tallinn, d1 >= 8))
        elif i == 6:
            s.add(Implies(seq[6] == Tallinn, d6 <= 12))
        else:
            s.add(Implies(seq[i] == Tallinn, And(days[i-1] <= 12, days[i] >= 8)))
    
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(7)]
        days_val = [m.evaluate(days[i]).as_long() for i in range(6)]
        
        itinerary_list = []
        
        # First city (index0)
        start0 = 1
        end0 = days_val[0]
        city0 = seq_val[0]
        if start0 == end0:
            itinerary_list.append({"day_range": "Day %d" % start0, "place": city_names[city0]})
        else:
            itinerary_list.append({"day_range": "Day %d-%d" % (start0, end0), "place": city_names[city0]})
        itinerary_list.append({"day_range": "Day %d" % end0, "place": city_names[city0]})
        city1 = seq_val[1]
        itinerary_list.append({"day_range": "Day %d" % end0, "place": city_names[city1]})
        
        # Middle cities: index1 to index5
        for i in range(1,6):
            start_i = days_val[i-1]
            end_i = days_val[i]
            city_i = seq_val[i]
            if start_i == end_i:
                itinerary_list.append({"day_range": "Day %d" % start_i, "place": city_names[city_i]})
            else:
                itinerary_list.append({"day_range": "Day %d-%d" % (start_i, end_i), "place": city_names[city_i]})
            itinerary_list.append({"day_range": "Day %d" % end_i, "place": city_names[city_i]})
            next_city = seq_val[i+1]
            itinerary_list.append({"day_range": "Day %d" % end_i, "place": city_names[next_city]})
        
        # Last city (index6)
        start6 = days_val[5]
        end6 = 26
        city6 = seq_val[6]
        if start6 == end6:
            itinerary_list.append({"day_range": "Day %d" % start6, "place": city_names[city6]})
        else:
            itinerary_list.append({"day_range": "Day %d-%d" % (start6, end6), "place": city_names[city6]})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()