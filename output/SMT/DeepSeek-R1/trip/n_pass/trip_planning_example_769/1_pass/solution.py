from z3 import *

def main():
    s1, s2, s3, s4, s5 = Ints('s1 s2 s3 s4 s5')
    c0, c1, c2, c3, c4, c5 = Strings('c0 c1 c2 c3 c4 c5')
    
    s = Solver()
    
    cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
    
    s.add(s1 >= 1, s1 <= 16)
    s.add(s2 >= s1, s2 <= 16)
    s.add(s3 >= s2, s3 <= 16)
    s.add(s4 >= s3, s4 <= 16)
    s.add(s5 >= s4, s5 <= 16)
    
    s.add(Or([c0 == city for city in cities]))
    s.add(Or([c1 == city for city in cities]))
    s.add(Or([c2 == city for city in cities]))
    s.add(Or([c3 == city for city in cities]))
    s.add(Or([c4 == city for city in cities]))
    s.add(Or([c5 == city for city in cities]))
    
    flights_str = [
        "Porto and Amsterdam",
        "Munich and Amsterdam",
        "Reykjavik and Amsterdam",
        "Munich and Porto",
        "Prague and Reykjavik",
        "Reykjavik and Munich",
        "Amsterdam and Santorini",
        "Prague and Amsterdam",
        "Prague and Munich"
    ]
    directed_flights = []
    for flight in flights_str:
        parts = flight.split(' and ')
        A = parts[0].strip()
        B = parts[1].strip()
        directed_flights.append((A, B))
        directed_flights.append((B, A))
    
    for i in range(5):
        constraints = []
        for (A, B) in directed_flights:
            constraints.append(And(c0 == A, c1 == B)) if i == 0 else None
            constraints.append(And(c1 == A, c2 == B)) if i == 1 else None
            constraints.append(And(c2 == A, c3 == B)) if i == 2 else None
            constraints.append(And(c3 == A, c4 == B)) if i == 3 else None
            constraints.append(And(c4 == A, c5 == B)) if i == 4 else None
        if i == 0:
            s.add(Or(constraints))
        elif i == 1:
            s.add(Or(constraints))
        elif i == 2:
            s.add(Or(constraints))
        elif i == 3:
            s.add(Or(constraints))
        elif i == 4:
            s.add(Or(constraints))
    
    total_Porto = 0
    total_Prague = 0
    total_Reykjavik = 0
    total_Santorini = 0
    total_Amsterdam = 0
    total_Munich = 0
    
    total_Porto += If(c0 == "Porto", s1, 0)
    total_Prague += If(c0 == "Prague", s1, 0)
    total_Reykjavik += If(c0 == "Reykjavik", s1, 0)
    total_Santorini += If(c0 == "Santorini", s1, 0)
    total_Amsterdam += If(c0 == "Amsterdam", s1, 0)
    total_Munich += If(c0 == "Munich", s1, 0)
    
    total_Porto += If(c1 == "Porto", s2 - s1 + 1, 0)
    total_Prague += If(c1 == "Prague", s2 - s1 + 1, 0)
    total_Reykjavik += If(c1 == "Reykjavik", s2 - s1 + 1, 0)
    total_Santorini += If(c1 == "Santorini", s2 - s1 + 1, 0)
    total_Amsterdam += If(c1 == "Amsterdam", s2 - s1 + 1, 0)
    total_Munich += If(c1 == "Munich", s2 - s1 + 1, 0)
    
    total_Porto += If(c2 == "Porto", s3 - s2 + 1, 0)
    total_Prague += If(c2 == "Prague", s3 - s2 + 1, 0)
    total_Reykjavik += If(c2 == "Reykjavik", s3 - s2 + 1, 0)
    total_Santorini += If(c2 == "Santorini", s3 - s2 + 1, 0)
    total_Amsterdam += If(c2 == "Amsterdam", s3 - s2 + 1, 0)
    total_Munich += If(c2 == "Munich", s3 - s2 + 1, 0)
    
    total_Porto += If(c3 == "Porto", s4 - s3 + 1, 0)
    total_Prague += If(c3 == "Prague", s4 - s3 + 1, 0)
    total_Reykjavik += If(c3 == "Reykjavik", s4 - s3 + 1, 0)
    total_Santorini += If(c3 == "Santorini", s4 - s3 + 1, 0)
    total_Amsterdam += If(c3 == "Amsterdam", s4 - s3 + 1, 0)
    total_Munich += If(c3 == "Munich", s4 - s3 + 1, 0)
    
    total_Porto += If(c4 == "Porto", s5 - s4 + 1, 0)
    total_Prague += If(c4 == "Prague", s5 - s4 + 1, 0)
    total_Reykjavik += If(c4 == "Reykjavik", s5 - s4 + 1, 0)
    total_Santorini += If(c4 == "Santorini", s5 - s4 + 1, 0)
    total_Amsterdam += If(c4 == "Amsterdam", s5 - s4 + 1, 0)
    total_Munich += If(c4 == "Munich", s5 - s4 + 1, 0)
    
    total_Porto += If(c5 == "Porto", 17 - s5, 0)
    total_Prague += If(c5 == "Prague", 17 - s5, 0)
    total_Reykjavik += If(c5 == "Reykjavik", 17 - s5, 0)
    total_Santorini += If(c5 == "Santorini", 17 - s5, 0)
    total_Amsterdam += If(c5 == "Amsterdam", 17 - s5, 0)
    total_Munich += If(c5 == "Munich", 17 - s5, 0)
    
    s.add(total_Porto == 5)
    s.add(total_Prague == 4)
    s.add(total_Reykjavik == 4)
    s.add(total_Santorini == 2)
    s.add(total_Amsterdam == 2)
    s.add(total_Munich == 4)
    
    ams14 = Or(
        And(14 <= s1, c0 == "Amsterdam"),
        And(s1 <= 14, 14 <= s2, c1 == "Amsterdam"),
        And(s2 <= 14, 14 <= s3, c2 == "Amsterdam"),
        And(s3 <= 14, 14 <= s4, c3 == "Amsterdam"),
        And(s4 <= 14, 14 <= s5, c4 == "Amsterdam"),
        And(s5 <= 14, c5 == "Amsterdam")
    )
    s.add(ams14)
    
    ams15 = Or(
        And(15 <= s1, c0 == "Amsterdam"),
        And(s1 <= 15, 15 <= s2, c1 == "Amsterdam"),
        And(s2 <= 15, 15 <= s3, c2 == "Amsterdam"),
        And(s3 <= 15, 15 <= s4, c3 == "Amsterdam"),
        And(s4 <= 15, 15 <= s5, c4 == "Amsterdam"),
        And(s5 <= 15, c5 == "Amsterdam")
    )
    s.add(ams15)
    
    wedding_conds = []
    for d in [4,5,6,7]:
        cond = Or(
            And(d <= s1, c0 == "Reykjavik"),
            And(s1 <= d, d <= s2, c1 == "Reykjavik"),
            And(s2 <= d, d <= s3, c2 == "Reykjavik"),
            And(s3 <= d, d <= s4, c3 == "Reykjavik"),
            And(s4 <= d, d <= s5, c4 == "Reykjavik"),
            And(s5 <= d, c5 == "Reykjavik")
        )
        wedding_conds.append(cond)
    s.add(Or(wedding_conds))
    
    meeting_conds = []
    for d in [7,8,9,10]:
        cond = Or(
            And(d <= s1, c0 == "Munich"),
            And(s1 <= d, d <= s2, c1 == "Munich"),
            And(s2 <= d, d <= s3, c2 == "Munich"),
            And(s3 <= d, d <= s4, c3 == "Munich"),
            And(s4 <= d, d <= s5, c4 == "Munich"),
            And(s5 <= d, c5 == "Munich")
        )
        meeting_conds.append(cond)
    s.add(Or(meeting_conds))
    
    if s.check() == sat:
        m = s.model()
        s1_val = m[s1].as_long()
        s2_val = m[s2].as_long()
        s3_val = m[s3].as_long()
        s4_val = m[s4].as_long()
        s5_val = m[s5].as_long()
        c0_val = m.eval(c0)
        c1_val = m.eval(c1)
        c2_val = m.eval(c2)
        c3_val = m.eval(c3)
        c4_val = m.eval(c4)
        c5_val = m.eval(c5)
        
        c0_val = c0_val.as_string() if is_string_value(c0_val) else str(c0_val)
        c1_val = c1_val.as_string() if is_string_value(c1_val) else str(c1_val)
        c2_val = c2_val.as_string() if is_string_value(c2_val) else str(c2_val)
        c3_val = c3_val.as_string() if is_string_value(c3_val) else str(c3_val)
        c4_val = c4_val.as_string() if is_string_value(c4_val) else str(c4_val)
        c5_val = c5_val.as_string() if is_string_value(c5_val) else str(c5_val)
        
        segments = []
        segments.append( (1, s1_val, c0_val) )
        segments.append( (s1_val, s2_val, c1_val) )
        segments.append( (s2_val, s3_val, c2_val) )
        segments.append( (s3_val, s4_val, c3_val) )
        segments.append( (s4_val, s5_val, c4_val) )
        segments.append( (s5_val, 16, c5_val) )
        
        itinerary = []
        for idx, seg in enumerate(segments):
            start, end, city = seg
            if start == end:
                day_range_str = "Day %d" % start
            else:
                day_range_str = "Day %d-%d" % (start, end)
            itinerary.append( {"day_range": day_range_str, "place": city} )
            if idx < 5:
                travel_day = end
                itinerary.append( {"day_range": "Day %d" % travel_day, "place": city} )
                itinerary.append( {"day_range": "Day %d" % travel_day, "place": segments[idx+1][2]} )
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

def is_string_value(v):
    return isinstance(v, StringVal)

if __name__ == "__main__":
    main()