import json
from itertools import permutations

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes: nested dictionary
    travel_times = {
        'Financial District': {
            'Chinatown': 5,
            'Golden Gate Park': 23
        },
        'Chinatown': {
            'Financial District': 5,
            'Golden Gate Park': 23
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Chinatown': 23
        }
    }
    
    # Friends data: availability and constraints
    friends = {
        'Barbara': {
            'location': 'Golden Gate Park',
            'available_start': 8*60 + 15,  # 8:15 AM
            'available_end': 19*60,         # 7:00 PM
            'min_duration': 45
        },
        'Kenneth': {
            'location': 'Chinatown',
            'available_start': 12*60,       # 12:00 PM
            'available_end': 15*60,          # 3:00 PM
            'min_duration': 90
        }
    }
    
    start_location = 'Financial District'
    start_time = 9*60  # 9:00 AM in minutes
    
    candidates = []
    friend_names = list(friends.keys())
    
    # Try all permutations for two friends
    for perm in permutations(friend_names):
        current_loc = start_location
        current_time = start_time
        schedule = []
        feasible = True
        
        for idx, friend in enumerate(perm):
            loc = friends[friend]['location']
            avail_start = friends[friend]['available_start']
            avail_end = friends[friend]['available_end']
            min_dur = friends[friend]['min_duration']
            
            # Travel to friend's location
            travel_duration = travel_times[current_loc][loc]
            current_time += travel_duration
            
            # Check if we arrived after availability ends
            if current_time > avail_end:
                feasible = False
                break
                
            # Start time for meeting: max of arrival and friend's availability start
            start_meeting = max(current_time, avail_start)
            
            # For next friend (if exists)
            if idx < len(perm) - 1:
                next_friend = perm[idx + 1]
                next_loc = friends[next_friend]['location']
                next_avail_start = friends[next_friend]['available_start']
                next_travel = travel_times[loc][next_loc]
                
                # Ideal arrival at next friend: next_avail_start
                ideal_arrival_next = next_avail_start
                ideal_departure = ideal_arrival_next - next_travel
                
                if ideal_departure < start_meeting:
                    # Meet for minimum duration
                    end_meeting = start_meeting + min_dur
                    if end_meeting > avail_end:
                        feasible = False
                        break
                    # Add meeting and update current time
                    schedule.append({
                        'action': 'meet',
                        'location': loc,
                        'person': friend,
                        'start_time': format_time(start_meeting),
                        'end_time': format_time(end_meeting)
                    })
                    current_time = end_meeting
                else:
                    # Meet until ideal departure if duration sufficient
                    meeting_duration = ideal_departure - start_meeting
                    if meeting_duration >= min_dur:
                        end_meeting = ideal_departure
                    else:
                        end_meeting = start_meeting + min_dur
                    
                    if end_meeting > avail_end:
                        feasible = False
                        break
                    
                    schedule.append({
                        'action': 'meet',
                        'location': loc,
                        'person': friend,
                        'start_time': format_time(start_meeting),
                        'end_time': format_time(end_meeting)
                    })
                    current_time = end_meeting
            else:
                # Last friend: meet for minimum duration
                end_meeting = start_meeting + min_dur
                if end_meeting > avail_end:
                    feasible = False
                    break
                
                schedule.append({
                    'action': 'meet',
                    'location': loc,
                    'person': friend,
                    'start_time': format_time(start_meeting),
                    'end_time': format_time(end_meeting)
                })
                current_time = end_meeting
            
            current_loc = loc
        
        if feasible:
            candidates.append((len(perm), current_time, schedule))
    
    # If no two-friend schedule found, try one friend
    if not candidates:
        for friend in friend_names:
            current_loc = start_location
            current_time = start_time
            schedule = []
            
            loc = friends[friend]['location']
            avail_start = friends[friend]['available_start']
            avail_end = friends[friend]['available_end']
            min_dur = friends[friend]['min_duration']
            
            # Travel to friend
            travel_duration = travel_times[current_loc][loc]
            current_time += travel_duration
            
            if current_time > avail_end:
                continue
                
            start_meeting = max(current_time, avail_start)
            end_meeting = start_meeting + min_dur
            
            if end_meeting > avail_end:
                continue
                
            schedule.append({
                'action': 'meet',
                'location': loc,
                'person': friend,
                'start_time': format_time(start_meeting),
                'end_time': format_time(end_meeting)
            })
            candidates.append((1, end_meeting, schedule))
    
    # Select best candidate: most friends, then earliest end time
    if candidates:
        candidates.sort(key=lambda x: (-x[0], x[1]))
        best_schedule = candidates[0][2]
    else:
        best_schedule = []
    
    # Output as JSON
    result = {"itinerary": best_schedule}
    print(json.dumps(result))

if __name__ == "__main__":
    main()