import json
import itertools

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    # Format without a leading zero for the hour and always two digits for minutes
    return f"{hours}:{minutes:02d}"

def main():
    # Define travel distances (in minutes) between locations
    travel_times = {
        'Sunset District': {
            'Russian Hill': 24,
            'Chinatown': 30,
            'Presidio': 16,
            "Fisherman's Wharf": 29
        },
        'Russian Hill': {
            'Sunset District': 23,
            'Chinatown': 9,
            'Presidio': 14,
            "Fisherman's Wharf": 7
        },
        'Chinatown': {
            'Sunset District': 29,
            'Russian Hill': 7,
            'Presidio': 19,
            "Fisherman's Wharf": 8
        },
        'Presidio': {
            'Sunset District': 15,
            'Russian Hill': 14,
            'Chinatown': 21,
            "Fisherman's Wharf": 19
        },
        "Fisherman's Wharf": {
            'Sunset District': 27,
            'Russian Hill': 7,
            'Chinatown': 12,
            'Presidio': 17
        }
    }
    
    # Define friends with meeting constraints.
    # Times are stored in minutes after midnight.
    friends = [
        {
            'person': 'William',
            'location': 'Russian Hill',
            'avail_start': 18 * 60 + 30,  # 18:30 -> 1110
            'avail_end': 20 * 60 + 45,    # 20:45 -> 1245
            'duration': 105              # required meeting minutes
        },
        {
            'person': 'Michelle',
            'location': 'Chinatown',
            'avail_start': 8 * 60 + 15,   # 8:15 -> 495
            'avail_end': 14 * 60,         # 14:00 -> 840
            'duration': 15
        },
        {
            'person': 'George',
            'location': 'Presidio',
            'avail_start': 10 * 60 + 30,  # 10:30 -> 630
            'avail_end': 18 * 60 + 45,    # 18:45 -> 1125
            'duration': 30
        },
        {
            'person': 'Robert',
            'location': "Fisherman's Wharf",
            'avail_start': 9 * 60,        # 9:00 -> 540
            'avail_end': 13 * 60 + 45,      # 13:45 -> 825
            'duration': 30
        }
    ]
    
    # Starting point: Sunset District at 9:00
    start_location = 'Sunset District'
    start_time = 9 * 60  # 9:00 AM -> 540 minutes
    
    # Since William's available window is in the evening, we fix him as the last meeting.
    william = next(friend for friend in friends if friend['person'] == 'William')
    other_friends = [friend for friend in friends if friend['person'] != 'William']
    
    best_itinerary = None
    best_wait_total = None

    # Evaluate all possible orders for the other 3 meetings.
    for perm in itertools.permutations(other_friends):
        itinerary = []
        current_time = start_time
        current_location = start_location
        wait_total = 0
        feasible = True

        # Schedule meetings in the current permutation order.
        for friend in perm:
            travel = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel
            meeting_start = max(arrival_time, friend['avail_start'])
            meeting_end = meeting_start + friend['duration']
            # Check if the meeting can finish before the person's departure.
            if meeting_end > friend['avail_end']:
                feasible = False
                break
            wait_total += max(0, meeting_start - arrival_time)
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['person'],
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']

        # Schedule William as the final meeting.
        if feasible:
            travel = travel_times[current_location][william['location']]
            arrival_time = current_time + travel
            meeting_start = max(arrival_time, william['avail_start'])
            meeting_end = meeting_start + william['duration']
            if meeting_end > william['avail_end']:
                feasible = False
            else:
                wait_total += max(0, meeting_start - arrival_time)
                itinerary.append({
                    "action": "meet",
                    "location": william['location'],
                    "person": william['person'],
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = william['location']

        # If the itinerary is feasible and includes all four meetings, consider it.
        if feasible and len(itinerary) == 4:
            # Use total idle waiting time as a tie-breaker (minimize waiting).
            if best_itinerary is None or wait_total < best_wait_total:
                best_itinerary = itinerary
                best_wait_total = wait_total

    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()