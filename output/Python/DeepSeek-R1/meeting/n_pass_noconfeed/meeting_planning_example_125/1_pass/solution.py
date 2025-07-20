import json
from itertools import permutations

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    # Define travel times between locations
    travel_times = {
        'Embarcadero': {
            'Financial District': 5,
            'Alamo Square': 19
        },
        'Financial District': {
            'Embarcadero': 4,
            'Alamo Square': 17
        },
        'Alamo Square': {
            'Embarcadero': 17,
            'Financial District': 17
        }
    }
    
    # Define friends with their constraints
    friends = [
        {
            'name': 'Stephanie',
            'location': 'Financial District',
            'start_min': 8 * 60 + 15,  # 8:15 AM
            'end_min': 11 * 60 + 30,   # 11:30 AM
            'min_duration': 90
        },
        {
            'name': 'John',
            'location': 'Alamo Square',
            'start_min': 10 * 60 + 15, # 10:15 AM
            'end_min': 20 * 60 + 45,   # 8:45 PM
            'min_duration': 30
        }
    ]
    
    # Starting point
    start_location = 'Embarcadero'
    start_time_min = 9 * 60  # 9:00 AM
    
    # Try all permutations of friends (both orders)
    best_schedule = None
    best_total_meeting_time = -1
    orders = list(permutations(friends, 2))
    
    for order in orders:
        A, B = order
        current_time = start_time_min
        current_loc = start_location
        
        # Travel to first friend
        if current_loc != A['location']:
            current_time += travel_times[current_loc][A['location']]
        
        # Meeting with first friend
        start_A = max(current_time, A['start_min'])
        end_A = A['end_min']
        duration_A = end_A - start_A
        if duration_A < A['min_duration']:
            continue  # Not enough time for friend A
        
        # Travel to second friend
        current_time = end_A
        if A['location'] != B['location']:
            current_time += travel_times[A['location']][B['location']]
        
        # Meeting with second friend
        start_B = max(current_time, B['start_min'])
        end_B = B['end_min']
        duration_B = end_B - start_B
        if duration_B < B['min_duration']:
            continue  # Not enough time for friend B
        
        total_meeting_time = duration_A + duration_B
        if total_meeting_time > best_total_meeting_time:
            best_total_meeting_time = total_meeting_time
            best_schedule = [
                {
                    "action": "meet",
                    "location": A['location'],
                    "person": A['name'],
                    "start_time": minutes_to_time(start_A),
                    "end_time": minutes_to_time(end_A)
                },
                {
                    "action": "meet",
                    "location": B['location'],
                    "person": B['name'],
                    "start_time": minutes_to_time(start_B),
                    "end_time": minutes_to_time(end_B)
                }
            ]
    
    # If no two-friend schedule works, try one friend
    if best_schedule is None:
        best_one_schedule = None
        best_one_meeting_time = -1
        for friend in friends:
            current_time = start_time_min
            current_loc = start_location
            if current_loc != friend['location']:
                current_time += travel_times[current_loc][friend['location']]
            
            start_meet = max(current_time, friend['start_min'])
            end_meet = friend['end_min']
            duration = end_meet - start_meet
            if duration >= friend['min_duration'] and duration > best_one_meeting_time:
                best_one_meeting_time = duration
                best_one_schedule = [{
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_meet),
                    "end_time": minutes_to_time(end_meet)
                }]
        
        if best_one_schedule is not None:
            best_schedule = best_one_schedule
        else:
            best_schedule = []  # No valid meeting
    
    # Output the result as JSON
    result = {"itinerary": best_schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()