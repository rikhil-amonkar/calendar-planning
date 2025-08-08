from z3 import *
import json

def min_to_time(minutes):
    h = 9 + minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Precomputed travel times (minutes) - symmetric based on problem description
    travel_FD_to = {
        "Nancy": 5,    # FD -> Chinatown
        "Mary": 17,    # FD -> Alamo Square
        "Jessica": 19  # FD -> Bayview
    }
    
    # Symmetric travel times between locations
    travel_between = {
        ("Nancy", "Mary"): 17,   # Chinatown <-> Alamo Square
        ("Mary", "Nancy"): 17,
        ("Nancy", "Jessica"): 22, # Chinatown <-> Bayview
        ("Jessica", "Nancy"): 22,
        ("Mary", "Jessica"): 16,  # Alamo Square <-> Bayview
        ("Jessica", "Mary"): 16
    }
    
    # Meeting data
    names = ["Nancy", "Mary", "Jessica"]
    durations = [90, 75, 45]  # minutes
    min_starts = [30, 0, 135]  # minutes after 9:00 AM
    max_ends = [270, 720, 285]  # minutes after 9:00 AM
    
    s = Solver()
    
    # Start time variables (minutes after 9:00 AM)
    start_nancy = Int('start_nancy')
    start_mary = Int('start_mary')
    start_jessica = Int('start_jessica')
    
    # Order indicator variables
    before_nm = Int('before_nm')  # 1 if Nancy before Mary, else 0
    before_nj = Int('before_nj')  # 1 if Nancy before Jessica, else 0
    before_mj = Int('before_mj')  # 1 if Mary before Jessica, else 0
    
    # Constraints for order indicators
    s.add(before_nm >= 0, before_nm <= 1)
    s.add(before_nj >= 0, before_nj <= 1)
    s.add(before_mj >= 0, before_mj <= 1)
    
    # Meeting time constraints
    s.add(start_nancy >= min_starts[0], start_nancy + durations[0] <= max_ends[0])
    s.add(start_mary >= min_starts[1], start_mary + durations[1] <= max_ends[1])
    s.add(start_jessica >= min_starts[2], start_jessica + durations[2] <= max_ends[2])
    
    # Travel time constraints based on meeting order
    # FD to first meeting constraints
    s.add(Or(
        And(before_nm == 1, before_nj == 1, start_nancy >= travel_FD_to["Nancy"]),
        And(before_mj == 1, before_nm == 0, start_mary >= travel_FD_to["Mary"]),
        And(before_nj == 0, before_mj == 0, start_jessica >= travel_FD_to["Jessica"])
    ))
    
    # Between meetings constraints
    s.add(If(before_nm == 1,
             start_mary >= start_nancy + durations[0] + travel_between[("Nancy", "Mary")],
             start_nancy >= start_mary + durations[1] + travel_between[("Mary", "Nancy")]))
    
    s.add(If(before_nj == 1,
             start_jessica >= start_nancy + durations[0] + travel_between[("Nancy", "Jessica")],
             start_nancy >= start_jessica + durations[2] + travel_between[("Jessica", "Nancy")]))
    
    s.add(If(before_mj == 1,
             start_jessica >= start_mary + durations[1] + travel_between[("Mary", "Jessica")],
             start_mary >= start_jessica + durations[2] + travel_between[("Jessica", "Mary")]))
    
    if s.check() == sat:
        m = s.model()
        # Get start times
        s_nancy = m[start_nancy].as_long()
        s_mary = m[start_mary].as_long()
        s_jessica = m[start_jessica].as_long()
        
        # Create meeting entries
        meetings = [
            {"person": "Nancy", "start": s_nancy, "end": s_nancy + durations[0]},
            {"person": "Mary", "start": s_mary, "end": s_mary + durations[1]},
            {"person": "Jessica", "start": s_jessica, "end": s_jessica + durations[2]}
        ]
        
        # Sort by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Build itinerary
        itinerary = []
        for meet in meetings:
            itinerary.append({
                "action": "meet",
                "person": meet["person"],
                "start_time": min_to_time(meet["start"]),
                "end_time": min_to_time(meet["end"])
            })
        
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()