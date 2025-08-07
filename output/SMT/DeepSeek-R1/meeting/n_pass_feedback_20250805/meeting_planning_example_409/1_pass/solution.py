from z3 import *
import json

def main():
    # Travel time matrix: 0: Fisherman's Wharf, 1: Bayview, 2: Golden Gate Park, 3: Nob Hill, 4: Marina District, 5: Embarcadero
    T = [
        [0, 26, 25, 11, 9, 8],
        [25, 0, 22, 20, 25, 19],
        [24, 23, 0, 20, 16, 25],
        [11, 19, 17, 0, 11, 9],
        [10, 27, 18, 12, 0, 14],
        [6, 21, 25, 10, 12, 0]
    ]
    
    # Meeting indices: 0: Laura, 1: Thomas, 2: Patricia, 3: Betty, 4: Stephanie
    meetings = [0, 1, 2, 3, 4]
    # Location indices for each meeting: Laura at Nob Hill (3), Thomas at Bayview (1), Patricia at Embarcadero (5), Betty at Marina (4), Stephanie at Golden Gate Park (2)
    locs = [3, 1, 5, 4, 2]
    # Minimum meeting durations in minutes
    min_time = [30, 120, 45, 45, 30]
    # Available start times in minutes from midnight
    available_start = [525, 930, 1050, 1125, 1110]
    # Available end times in minutes from midnight
    available_end = [975, 1110, 1320, 1305, 1305]
    # Friend names
    friends = ["Laura", "Thomas", "Patricia", "Betty", "Stephanie"]
    
    s = Solver()
    
    # Define permutation variables for meeting order
    P = [Int('P_%d' % i) for i in range(5)]
    for i in range(5):
        s.add(P[i] >= 0, P[i] < 5)
    s.add(Distinct(P))
    
    # Define start time, end time, and duration variables for each meeting
    S = [Real('S_%d' % i) for i in range(5)]
    E = [Real('E_%d' % i) for i in range(5)]
    d = [Real('d_%d' % i) for i in range(5)]
    
    # Add constraints for each meeting
    for i in range(5):
        s.add(d[i] >= min_time[i])
        s.add(S[i] >= available_start[i])
        s.add(E[i] <= available_end[i])
        s.add(E[i] == S[i] + d[i])
    
    # Constraints for the first meeting: start time at Fisherman's Wharf (0) plus travel to first location
    first_meeting = P[0]
    s.add(S[first_meeting] >= 540 + T[0][locs[first_meeting]])
    
    # Constraints for subsequent meetings
    for i in range(1, 5):
        prev_meeting = P[i-1]
        curr_meeting = P[i]
        travel = T[locs[prev_meeting]][locs[curr_meeting]]
        s.add(S[curr_meeting] >= E[prev_meeting] + travel)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract meeting times and friend names
        schedule = []
        for i in range(5):
            start_val = m.evaluate(S[i])
            end_val = m.evaluate(E[i])
            start_min = int(round(float(start_val.as_fraction())))
            end_min = int(round(float(end_val.as_fraction())))
            schedule.append((start_min, end_min, friends[i]))
        
        # Sort meetings by start time
        schedule.sort(key=lambda x: x[0])
        
        # Convert times to HH:MM format
        itinerary = []
        for start, end, friend in schedule:
            start_str = f"{start//60:02d}:{start%60:02d}"
            end_str = f"{end//60:02d}:{end%60:02d}"
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output the itinerary as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('No solution found')

if __name__ == "__main__":
    main()