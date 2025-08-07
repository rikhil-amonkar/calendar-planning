import z3
import json

def main():
    s_naples, e_naples, s_vienna, e_vienna, s_vilnius, e_vilnius = z3.Ints('s_naples e_naples s_vienna e_vienna s_vilnius e_vilnius')
    solver = z3.Solver()
    
    # Naples segment: 5 days including days 1-5
    solver.add(s_naples == 1)
    solver.add(e_naples == s_naples + 4)  # 5 days: s_naples to s_naples+4 (inclusive)
    
    # Vienna segment: 7 days starting at the end of Naples
    solver.add(s_vienna == e_naples)
    solver.add(e_vienna == s_vienna + 6)  # 7 days: s_vienna to s_vienna+6 (inclusive)
    
    # Vilnius segment: 7 days starting at the end of Vienna
    solver.add(s_vilnius == e_vienna)
    solver.add(e_vilnius == s_vilnius + 6)  # 7 days: s_vilnius to s_vilnius+6 (inclusive)
    
    # Total trip must end on day 17
    solver.add(e_vilnius == 17)
    
    if solver.check() == z3.sat:
        m = solver.model()
        s_naples_val = m[s_naples].as_long()
        e_naples_val = m[e_naples].as_long()
        s_vienna_val = m[s_vienna].as_long()
        e_vienna_val = m[e_vienna].as_long()
        s_vilnius_val = m[s_vilnius].as_long()
        e_vilnius_val = m[e_vilnius].as_long()
        
        itinerary = []
        
        # Naples: days from start to end-1 (exclusive of end)
        for day in range(s_naples_val, e_naples_val):
            itinerary.append({"day": day, "city": "Naples"})
        
        # Flight day from Naples to Vienna: day e_naples_val (counts for both)
        itinerary.append({"day": e_naples_val, "city": "Naples"})
        itinerary.append({"day": e_naples_val, "city": "Vienna"})
        
        # Vienna: days from e_naples_val+1 to e_vienna_val-1
        for day in range(e_naples_val + 1, e_vienna_val):
            itinerary.append({"day": day, "city": "Vienna"})
        
        # Flight day from Vienna to Vilnius: day e_vienna_val (counts for both)
        itinerary.append({"day": e_vienna_val, "city": "Vienna"})
        itinerary.append({"day": e_vienna_val, "city": "Vilnius"})
        
        # Vilnius: days from e_vienna_val+1 to e_vilnius_val (inclusive)
        for day in range(e_vienna_val + 1, e_vilnius_val + 1):
            itinerary.append({"day": day, "city": "Vilnius"})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()