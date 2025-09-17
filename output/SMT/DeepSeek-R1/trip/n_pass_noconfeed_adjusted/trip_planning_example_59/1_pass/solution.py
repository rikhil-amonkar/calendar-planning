from z3 import *

def main():
    # Define the cities
    B, L, P = 0, 1, 2
    city_names = {B: "Bucharest", L: "Lyon", P: "Porto"}
    
    # Create solver
    s = Solver()
    
    # Sequence of cities (3 segments)
    seq0 = Int('seq0')
    seq1 = Int('seq1')
    seq2 = Int('seq2')
    sequence = [seq0, seq1, seq2]
    
    # Only two possible sequences: [B, L, P] or [P, L, B]
    s.add(Or(
        And(seq0 == B, seq1 == L, seq2 == P),
        And(seq0 == P, seq1 == L, seq2 == B)
    ))
    
    # Days in each segment (pure days without travel)
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    s.add(s1 >= 0, s2 >= 0, s3 >= 0)
    s.add(s1 + s2 + s3 + 2 == 16)  # 2 travel days
    
    # City-day constraints
    bucharest_days = Int('bucharest_days')
    lyon_days = Int('lyon_days')
    porto_days = Int('porto_days')
    
    # Define city-days based on sequence
    s.add(Or(
        And(seq0 == B, seq1 == L, seq2 == P,
            bucharest_days == s1 + 1,
            lyon_days == s2 + 2,
            porto_days == s3 + 1),
        And(seq0 == P, seq1 == L, seq2 == B,
            porto_days == s1 + 1,
            lyon_days == s2 + 2,
            bucharest_days == s3 + 1)
    ))
    
    # Required days per city
    s.add(bucharest_days == 7, lyon_days == 7, porto_days == 4)
    
    # Wedding constraint: must be in Bucharest between day 1 and 7
    wedding_constraint = False
    for d in range(1, 8):
        # Check if in Bucharest on day d
        in_bucharest = Or(
            And(d <= s1 + 1, seq0 == B),  # segment1 or travel1
            And(s1 + 1 < d, d <= s1 + s2 + 2, seq1 == B),  # segment2 or travel2
            And(s1 + s2 + 2 < d, d <= s1 + s2 + s3 + 2, seq2 == B)  # segment3
        )
        wedding_constraint = Or(wedding_constraint, in_bucharest)
    s.add(wedding_constraint)
    
    # Check feasibility
    if s.check() == sat:
        model = s.model()
        # Extract values
        s1_val = model.eval(s1).as_long()
        s2_val = model.eval(s2).as_long()
        s3_val = model.eval(s3).as_long()
        seq0_val = model.eval(seq0).as_long()
        seq1_val = model.eval(seq1).as_long()
        seq2_val = model.eval(seq2).as_long()
        
        # Map segments to city names
        seg1_city = city_names[seq0_val]
        seg2_city = city_names[seq1_val]
        seg3_city = city_names[seq2_val]
        
        # Calculate day ranges
        seg1_start = 1
        seg1_end = s1_val
        travel1_day = seg1_end + 1
        seg2_start = travel1_day + 1
        seg2_end = seg2_start + s2_val - 1
        travel2_day = seg2_end + 1
        seg3_start = travel2_day + 1
        seg3_end = seg3_start + s3_val - 1
        
        # Build itinerary
        itinerary = []
        
        # Segment 1
        if s1_val > 0:
            day_range = f"Day {seg1_start}-{seg1_end}" if s1_val > 1 else f"Day {seg1_start}"
            itinerary.append({"day_range": day_range, "place": seg1_city})
        
        # Travel day 1
        travel_place = f"{seg1_city} and {seg2_city}"
        itinerary.append({"day_range": f"Day {travel1_day}", "place": travel_place})
        
        # Segment 2
        if s2_val > 0:
            day_range = f"Day {seg2_start}-{seg2_end}" if s2_val > 1 else f"Day {seg2_start}"
            itinerary.append({"day_range": day_range, "place": seg2_city})
        
        # Travel day 2
        travel_place = f"{seg2_city} and {seg3_city}"
        itinerary.append({"day_range": f"Day {travel2_day}", "place": travel_place})
        
        # Segment 3
        if s3_val > 0:
            day_range = f"Day {seg3_start}-{seg3_end}" if s3_val > 1 else f"Day {seg3_start}"
            itinerary.append({"day_range": day_range, "place": seg3_city})
        
        # Output as JSON
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()