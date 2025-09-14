from z3 import *
import json

def minutes_to_str(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object from Z3
    opt = Optimize()
    
    # Define integer variables for the start and end times (in minutes from midnight)
    h_start = Int("h_start")  # Helen meeting start time (North Beach)
    h_end   = Int("h_end")    # Helen meeting end time
    k_start = Int("k_start")  # Kimberly meeting start time (Fisherman's Wharf)
    k_end   = Int("k_end")    # Kimberly meeting end time
    p_start = Int("p_start")  # Patricia meeting start time (Bayview)
    p_end   = Int("p_end")    # Patricia meeting end time
    finish  = Int("finish")   # Overall finish time (max among meeting end times)

    # Meeting duration constraints
    opt.add(h_end - h_start >= 120)  # Helen: minimum 120 minutes
    opt.add(k_end - k_start >= 45)   # Kimberly: minimum 45 minutes
    opt.add(p_end - p_start >= 120)  # Patricia: minimum 120 minutes

    # Availability windows and travel from starting point (Nob Hill at 9:00 AM => 540 minutes)
    # For Helen: Meeting at North Beach with travel time 8 minutes from Nob Hill. 
    # Helen is available 7:00 (420 minutes) to 16:45 (1005 minutes).
    opt.add(h_start >= 540 + 8)  # Must arrive at North Beach no earlier than 548 minutes.
    opt.add(h_end <= 1005)
    
    # For Kimberly: Meeting at Fisherman's Wharf with travel time 11 minutes from Nob Hill.
    # Kimberly is available from 16:30 (990 minutes) to 21:00 (1260 minutes).
    opt.add(k_start >= max(540 + 11, 990))  # This forces k_start >= 990.
    opt.add(k_end <= 1260)
    
    # For Patricia: Meeting at Bayview with travel time 19 minutes from Nob Hill.
    # Patricia is available from 18:00 (1080 minutes) to 21:15 (1275 minutes).
    opt.add(p_start >= max(540 + 19, 1080))  # p_start >= 1080.
    opt.add(p_end <= 1275)
    
    # Non-overlapping meeting constraints with travel times between meeting locations.
    # Travel times (in minutes):
    #   Nob Hill -> North Beach: 8, Nob Hill -> Fisherman's Wharf: 11, Nob Hill -> Bayview: 19.
    #   North Beach -> Fisherman's Wharf: 5, North Beach -> Bayview: 22.
    #   Fisherman's Wharf -> North Beach: 6, Fisherman's Wharf -> Bayview: 26.
    #   Bayview -> North Beach: 21, Bayview -> Fisherman's Wharf: 25.
    
    # For each pair of meetings, enforce that one occurs before the other with sufficient travel time.
    # Helen (North Beach) and Kimberly (Fisherman's Wharf):
    opt.add(Or(
        h_end + 5 <= k_start,  # Helen then Kimberly (travel North Beach -> Fisherman's Wharf: 5 min)
        k_end + 6 <= h_start   # Kimberly then Helen (travel Fisherman's Wharf -> North Beach: 6 min)
    ))
    
    # Helen (North Beach) and Patricia (Bayview):
    opt.add(Or(
        h_end + 22 <= p_start,  # Helen then Patricia (travel North Beach -> Bayview: 22 min)
        p_end + 21 <= h_start   # Patricia then Helen (travel Bayview -> North Beach: 21 min)
    ))
    
    # Kimberly (Fisherman's Wharf) and Patricia (Bayview):
    opt.add(Or(
        k_end + 26 <= p_start,  # Kimberly then Patricia (travel Fisherman's Wharf -> Bayview: 26 min)
        p_end + 25 <= k_start   # Patricia then Kimberly (travel Bayview -> Fisherman's Wharf: 25 min)
    ))
    
    # Define the overall finish time as at least the end of every meeting
    opt.add(finish >= h_end, finish >= k_end, finish >= p_end)
    
    # Objective: minimize the overall finish time for an optimal itinerary
    opt.minimize(finish)
    
    # Solve the scheduling problem
    if opt.check() == sat:
        m = opt.model()
        # Extract the meeting times from the model
        h_s = m[h_start].as_long()
        h_e = m[h_end].as_long()
        k_s = m[k_start].as_long()
        k_e = m[k_end].as_long()
        p_s = m[p_start].as_long()
        p_e = m[p_end].as_long()
        
        # Create a list of meetings with their details
        events = [
            {"person": "Helen",    "location": "North Beach",       "start": h_s, "end": h_e},
            {"person": "Kimberly", "location": "Fisherman's Wharf", "start": k_s, "end": k_e},
            {"person": "Patricia", "location": "Bayview",           "start": p_s, "end": p_e},
        ]
        
        # Sort events in chronological order by start time
        events.sort(key=lambda evt: evt["start"])
        
        # Construct the itinerary with formatted time strings
        itinerary = []
        for evt in events:
            itinerary.append({
                "action": "meet",
                "location": evt["location"],
                "person": evt["person"],
                "start_time": minutes_to_str(evt["start"]),
                "end_time": minutes_to_str(evt["end"])
            })
        
        # Output the result as a JSON-formatted dictionary
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No valid schedule found"}))

if __name__ == "__main__":
    main()