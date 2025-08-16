from z3 import *
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()
    
    # Define time variables in minutes from midnight.
    # 9:00 AM = 540, 12:45 PM = 765, 14:00 = 840, 15:15 = 915.
    TS_j = Int('TS_j')  # start time for James meeting (at Mission District)
    TE_j = Int('TE_j')  # end time for James meeting
    TS_r = Int('TS_r')  # start time for Robert meeting (at The Castro)
    TE_r = Int('TE_r')  # end time for Robert meeting

    # Add constraints for James:
    # James is available at Mission District from 12:45 (765) to 14:00 (840)
    # and you want to meet him for at least 75 minutes.
    opt.add(TS_j >= 765)        # cannot start before 12:45
    opt.add(TE_j <= 840)        # must finish by 14:00
    opt.add(TE_j - TS_j >= 75)  # meeting must last at least 75 minutes

    # Add constraints for Robert:
    # Robert is available at The Castro from 12:45 (765) to 15:15 (915)
    # and you want to meet him for at least 30 minutes.
    opt.add(TS_r >= 765)         # cannot start before 12:45
    opt.add(TE_r <= 915)         # must finish by 15:15
    opt.add(TE_r - TS_r >= 30)   # meeting must last at least 30 minutes

    # Travel constraints:
    # Starting at North Beach at 9:00 (540 minutes)
    # Travel from North Beach to Mission District takes 18 minutes.
    # Thus, you cannot start the meeting with James before 540+18 = 558.
    opt.add(TS_j >= 540 + 18)
    
    # After finishing meeting James at Mission District, you must travel
    # from Mission District to The Castro, which takes 7 minutes.
    # Thus, the start time of the Robert meeting must be at least TE_j + 7.
    opt.add(TS_r >= TE_j + 7)
    
    # We want to “optimize” by finishing our schedule as early as possible.
    # Minimizing TE_r (the end time of Robert’s meeting) encourages the earliest finish.
    opt.minimize(TE_r)
    
    if opt.check() == sat:
        model = opt.model()
        ts_j = model[TS_j].as_long()
        te_j = model[TE_j].as_long()
        ts_r = model[TS_r].as_long()
        te_r = model[TE_r].as_long()
        
        # Construct the itinerary as required.
        itinerary = [
            {
                "action": "meet",
                "person": "James",
                "start_time": minutes_to_time(ts_j),
                "end_time": minutes_to_time(te_j)
            },
            {
                "action": "meet",
                "person": "Robert",
                "start_time": minutes_to_time(ts_r),
                "end_time": minutes_to_time(te_r)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=4))
    else:
        print("No solution found")
        
if __name__ == '__main__':
    main()