from z3 import *
import json

def main():
    # Meeting data: index, friend, district, available_start (minutes from 9:00 AM), available_end (minutes from 9:00 AM), min_duration
    meetings = [
        (0, "Elizabeth", "Financial District", 60, 225, 75),
        (1, "Joseph", "Union Square", 165, 345, 120),
        (2, "Ashley", "Russian Hill", 150, 750, 45),
        (3, "Karen", "Mission District", 315, 780, 30),
        (4, "Richard", "Fisherman's Wharf", 330, 510, 30),
        (5, "Kimberly", "Haight-Ashbury", 315, 510, 105),
        (6, "Helen", "Sunset District", 345, 705, 105),
        (7, "Robert", "Presidio", 765, 825, 60)
    ]
    
    districts = [meeting[2] for meeting in meetings]
    
    # Travel times dictionary
    travel_times = {
        "Marina District": {
            "Mission District": 20,
            "Fisherman's Wharf": 10,
            "Presidio": 10,
            "Union Square": 16,
            "Sunset District": 19,
            "Financial District": 17,
            "Haight-Ashbury": 16,
            "Russian Hill": 8
        },
        "Mission District": {
            "Marina District": 19,
            "Fisherman's Wharf": 22,
            "Presidio": 25,
            "Union Square": 15,
            "Sunset District": 24,
            "Financial District": 15,
            "Haight-Ashbury": 12,
            "Russian Hill": 15
        },
        "Fisherman's Wharf": {
            "Marina District": 9,
            "Mission District": 22,
            "Presidio": 17,
            "Union Square": 13,
            "Sunset District": 27,
            "Financial District": 11,
            "Haight-Ashbury": 22,
            "Russian Hill": 7
        },
        "Presidio": {
            "Marina District": 11,
            "Mission District": 26,
            "Fisherman's Wharf": 19,
            "Union Square": 22,
            "Sunset District": 15,
            "Financial District": 23,
            "Haight-Ashbury": 15,
            "Russian Hill": 14
        },
        "Union Square": {
            "Marina District": 18,
            "Mission District": 14,
            "Fisherman's Wharf": 15,
            "Presidio": 24,
            "Sunset District": 27,
            "Financial District": 9,
            "Haight-Ashbury": 18,
            "Russian Hill": 13
        },
        "Sunset District": {
            "Marina District": 21,
            "Mission District": 25,
            "Fisherman's Wharf": 29,
            "Presidio": 16,
            "Union Square": 30,
            "Financial District": 30,
            "Haight-Ashbury": 15,
            "Russian Hill": 24
        },
        "Financial District": {
            "Marina District": 15,
            "Mission District": 17,
            "Fisherman's Wharf": 10,
            "Presidio": 22,
            "Union Square": 9,
            "Sunset District": 30,
            "Haight-Ashbury": 19,
            "Russian Hill": 11
        },
        "Haight-Ashbury": {
            "Marina District": 17,
            "Mission District": 11,
            "Fisherman's Wharf": 23,
            "Presidio": 15,
            "Union Square": 19,
            "Sunset District": 15,
            "Financial District": 21,
            "Russian Hill": 17
        },
        "Russian Hill": {
            "Marina District": 7,
            "Mission District": 16,
            "Fisherman's Wharf": 7,
            "Presidio": 14,
            "Union Square": 10,
            "Sunset District": 23,
            "Financial District": 11,
            "Haight-Ashbury": 17
        }
    }
    
    # Precompute travel_matrix[i][j]: travel time from district of meeting i to district of meeting j
    travel_matrix = [[0] * 8 for _ in range(8)]
    for i in range(8):
        for j in range(8):
            from_dist = meetings[i][2]
            to_dist = meetings[j][2]
            travel_matrix[i][j] = travel_times[from_dist][to_dist]
    
    # Precompute marina_travel[i]: travel time from Marina to district of meeting i
    marina_travel = [travel_times["Marina District"][meetings[i][2]] for i in range(8)]
    
    # Create Z3 solver
    s = Solver()
    
    # Meeting start times (in minutes from 9:00 AM)
    start_time = [Int(f'start_{i}') for i in range(8)]
    # End times
    end_time = [start_time[i] + meetings[i][5] for i in range(8)]
    
    # Position variables: which meeting is at position k (0 to 7)
    meeting_at_position = [Int(f'map_{k}') for k in range(8)]
    
    # Each meeting_at_position[k] must be between 0 and 7
    for k in range(8):
        s.add(meeting_at_position[k] >= 0, meeting_at_position[k] < 8)
    
    # All meetings_at_position are distinct
    s.add(Distinct(meeting_at_position))
    
    # Time window constraints for each meeting
    for i, (_, _, _, avail_start, avail_end, dur) in enumerate(meetings):
        s.add(start_time[i] >= avail_start)
        s.add(end_time[i] <= avail_end)
    
    # Travel time constraints
    # For the first meeting (at position 0)
    first_meeting = meeting_at_position[0]
    for i in range(8):
        s.add(Implies(first_meeting == i, start_time[i] >= marina_travel[i]))
    
    # For consecutive positions
    for pos in range(7):
        i_var = meeting_at_position[pos]
        j_var = meeting_at_position[pos+1]
        for i in range(8):
            for j in range(8):
                # If i_var is i and j_var is j, then require start_time[j] >= end_time[i] + travel_matrix[i][j]
                s.add(Implies(And(i_var == i, j_var == j), start_time[j] >= end_time[i] + travel_matrix[i][j]))
    
    # Check for satisfiability
    if s.check() == sat:
        model = s.model()
        # Extract start times
        start_times_min = []
        for i in range(8):
            start_val = model[start_time[i]]
            if isinstance(start_val, IntNumRef):
                start_times_min.append(start_val.as_long())
            else:
                start_times_min.append(model.evaluate(start_time[i]).as_long())
        
        # Build the itinerary
        itinerary = []
        for i, (_, friend, _, _, _, dur) in enumerate(meetings):
            start_min = start_times_min[i]
            end_min = start_min + dur
            # Convert to absolute time (minutes from midnight)
            base_minutes = 9 * 60  # 9:00 AM in minutes from midnight
            abs_start_min = base_minutes + start_min
            abs_end_min = base_minutes + end_min
            # Convert to HH:MM
            start_hour = abs_start_min // 60
            start_minute = abs_start_min % 60
            end_hour = abs_end_min // 60
            end_minute = abs_end_min % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Sort itinerary by start time
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        
        # Output as JSON
        result = {"itinerary": itinerary_sorted}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()