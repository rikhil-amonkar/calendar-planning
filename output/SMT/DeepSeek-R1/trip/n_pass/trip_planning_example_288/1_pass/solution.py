from z3 import Solver, Int, sat

def main():
    s = Solver()
    
    # Define variables for Madrid and Vienna
    Ma_start = Int('Ma_start')
    Ma_end = Int('Ma_end')
    V_start = Int('V_start')
    V_end = Int('V_end')
    
    # Constraints
    s.add(Ma_start == 7)
    s.add(Ma_end - Ma_start + 1 == 4)  # Madrid stay duration
    s.add(V_end == 11)
    s.add(V_end - V_start + 1 == 2)    # Vienna stay duration
    s.add(Ma_end == V_start)           # Fly from Madrid to Vienna on the same day Madrid ends
    
    if s.check() == sat:
        m = s.model()
        ma_s = m[Ma_start].as_long()
        ma_e = m[Ma_end].as_long()
        v_s = m[V_start].as_long()
        v_e = m[V_end].as_long()
        
        # Build itinerary
        itinerary = [
            {"day_range": "Day 1-7", "place": "Manchester"},
            {"day_range": "Day 7", "place": "Manchester"},
            {"day_range": "Day 7", "place": "Madrid"},
            {"day_range": f"Day {ma_s}-{ma_e}", "place": "Madrid"},
            {"day_range": f"Day {ma_e}", "place": "Madrid"},
            {"day_range": f"Day {v_s}", "place": "Vienna"},
            {"day_range": f"Day {v_s}-{v_e}", "place": "Vienna"},
            {"day_range": f"Day {v_e}", "place": "Vienna"},
            {"day_range": "Day 11", "place": "Stuttgart"},
            {"day_range": "Day 11-15", "place": "Stuttgart"}
        ]
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()