from z3 import *
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # We'll use minutes past midnight for all time variables.
    # Fixed known times:
    # Arrival at Sunset District is 09:00 = 540.
    # Friend availability windows (in minutes):
    # Daniel (Golden Gate Park): [08:00 (480), 13:30 (810)], need ≥15 minutes.
    # Margaret (Russian Hill): [09:00 (540), 16:00 (960)], need ≥30 minutes.
    # Charles (Alamo Square): [18:00 (1080), 20:45 (1245)], need ≥90 minutes.
    # Stephanie (Mission District): [20:30 (1230), 22:00 (1320)], need ≥90 minutes.
    
    # Travel times (in minutes). Note: these are asymmetric.
    travel = {
        ('Sunset','Alamo'): 17,
        ('Sunset','Russian'): 24,
        ('Sunset','Golden'): 11,
        ('Sunset','Mission'): 24,
        
        ('Alamo','Sunset'): 16,
        ('Alamo','Russian'): 13,
        ('Alamo','Golden'): 9,
        ('Alamo','Mission'): 10,
        
        ('Russian','Sunset'): 23,
        ('Russian','Alamo'): 15,
        ('Russian','Golden'): 21,
        ('Russian','Mission'): 16,
        
        ('Golden','Sunset'): 10,
        ('Golden','Alamo'): 10,
        ('Golden','Russian'): 19,
        ('Golden','Mission'): 17,
        
        ('Mission','Sunset'): 24,
        ('Mission','Alamo'): 11,
        ('Mission','Russian'): 15,
        ('Mission','Golden'): 17
    }
    
    # Locations for meetings:
    # Daniel: Golden Gate Park ("Golden")
    # Margaret: Russian Hill ("Russian")
    # Charles: Alamo Square ("Alamo")
    # Stephanie: Mission District ("Mission")
    # Starting location: Sunset District ("Sunset")
    
    opt = Optimize()
    
    # Define start time variables for the meetings we plan to schedule.
    # We let the solver pick meeting start times (in minutes past midnight)
    s_D = Int('s_D')  # Start time for Daniel meeting at Golden Gate Park.
    s_M = Int('s_M')  # Start time for Margaret meeting at Russian Hill.
    s_C = Int('s_C')  # Start time for Charles meeting at Alamo Square.
    # For Stephanie, because her available window (1230-1320) is tight for a 90-minute meeting,
    # we fix the meeting to start at 1230.
    s_S = 1230     
    
    # Meeting durations (fixed to the minimum required)
    d_D = 15
    d_M = 30
    d_C = 90
    d_S = 90  # For Stephanie; 1230 to 1320.
    
    # Compute end times.
    e_D = s_D + d_D  
    e_M = s_M + d_M  
    e_C = s_C + d_C  
    e_S = s_S + d_S  # This equals 1320.
    
    # -------------------------
    # Add constraints for each meeting.
    # -------------------------
    
    # -------------------------
    # Daniel (Golden Gate Park):
    # We are at Sunset at 09:00 (540). To go to Golden Gate Park,
    # travel time from Sunset -> Golden is 11 minutes.
    # So Daniel's meeting cannot start before 540 + 11 = 551.
    opt.add(s_D >= 540 + travel[('Sunset','Golden')])
    # Also Daniel is available from 08:00 (480) until 13:30 (810):
    opt.add(s_D >= 480)
    opt.add(e_D <= 810)
    # Meeting duration is fixed to 15 minutes.
    
    # -------------------------
    # Margaret (Russian Hill):
    # After finishing Daniel's meeting, we travel from Golden -> Russian.
    # Travel time from Golden to Russian is 19 minutes.
    opt.add(s_M >= e_D + travel[('Golden','Russian')])
    # Margaret's availability window is [09:00 (540), 16:00 (960)].
    opt.add(s_M >= 540)
    opt.add(e_M <= 960)
    # Meeting duration is fixed to 30 minutes.
    
    # -------------------------
    # Charles (Alamo Square):
    # After Margaret's meeting, travel from Russian -> Alamo takes 15 minutes.
    opt.add(s_C >= e_M + travel[('Russian','Alamo')])
    # Charles is available from 18:00 (1080) to 20:45 (1245):
    opt.add(s_C >= 1080)
    opt.add(e_C <= 1245)
    # Meeting duration is fixed to 90 minutes.
    # Additionally, to catch Stephanie in time,
    # we need to travel from Alamo -> Mission District (10 minutes)
    # so that Charles's meeting end plus travel is no later than 1230.
    opt.add(e_C + travel[('Alamo','Mission')] <= 1230)
    
    # -------------------------
    # Stephanie (Mission District):
    # Her window is [20:30 (1230), 22:00 (1320)] and the meeting must last 90 minutes.
    # The only possibility is to meet exactly from 1230 to 1320.
    # We already fixed s_S = 1230 and d_S = 90.
    
    # -------------------------
    # (Optional) To reduce idle waiting time, we can have an objective.
    # For example, minimize the gap between Charles's available start (1080) and his scheduled start.
    # This is optional since any feasible schedule meeting all constraints is acceptable.
    opt.minimize(s_C - 1080)
    
    # Check for a solution.
    if opt.check() == sat:
        m = opt.model()
        s_D_val = m[s_D].as_long()
        s_M_val = m[s_M].as_long()
        s_C_val = m[s_C].as_long()
        
        itinerary = []
        # Meeting with Daniel at Golden Gate Park.
        itinerary.append({
            "action": "meet",
            "person": "Daniel",
            "start_time": format_time(s_D_val),
            "end_time": format_time(s_D_val + d_D)
        })
        # Meeting with Margaret at Russian Hill.
        itinerary.append({
            "action": "meet",
            "person": "Margaret",
            "start_time": format_time(s_M_val),
            "end_time": format_time(s_M_val + d_M)
        })
        # Meeting with Charles at Alamo Square.
        itinerary.append({
            "action": "meet",
            "person": "Charles",
            "start_time": format_time(s_C_val),
            "end_time": format_time(s_C_val + d_C)
        })
        # Meeting with Stephanie at Mission District.
        itinerary.append({
            "action": "meet",
            "person": "Stephanie",
            "start_time": format_time(s_S),
            "end_time": format_time(s_S + d_S)
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=4))
    else:
        print("No feasible schedule found.")

if __name__ == "__main__":
    main()