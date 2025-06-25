from z3 import Solver, Int, sat

def main():
    s = Solver()
    s1 = Int('s1')  # start day for Naples
    e1 = Int('e1')  # end day for Naples
    s2 = Int('s2')  # start day for Vienna
    e2 = Int('e2')  # end day for Vienna
    s3 = Int('s3')  # start day for Vilnius
    e3 = Int('e3')  # end day for Vilnius

    s.add(s1 == 1)  # Naples stay starts on day 1
    s.add(e1 == s1 + 4)  # 5 days in Naples: days 1 to 5
    s.add(s2 == e1)  # Fly from Naples to Vienna on day e1 (5), arrive same day
    s.add(e2 == s2 + 6)  # 7 days in Vienna: days 5 to 11
    s.add(s3 == e2)  # Fly from Vienna to Vilnius on day e2 (11), arrive same day
    s.add(e3 == s3 + 6)  # 7 days in Vilnius: days 11 to 17
    s.add(e3 == 17)  # Trip ends on day 17

    if s.check() == sat:
        m = s.model()
        s1_val = m[s1].as_long()
        e1_val = m[e1].as_long()
        s2_val = m[s2].as_long()
        e2_val = m[e2].as_long()
        s3_val = m[s3].as_long()
        e3_val = m[e3].as_long()
        
        itinerary = [
            {"day_range": f"Day {s1_val}-{e1_val}", "place": "Naples"},
            {"day_range": f"Day {e1_val}", "place": "Naples"},
            {"day_range": f"Day {s2_val}", "place": "Vienna"},
            {"day_range": f"Day {s2_val}-{e2_val}", "place": "Vienna"},
            {"day_range": f"Day {e2_val}", "place": "Vienna"},
            {"day_range": f"Day {s3_val}", "place": "Vilnius"},
            {"day_range": f"Day {s3_val}-{e3_val}", "place": "Vilnius"}
        ]
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()