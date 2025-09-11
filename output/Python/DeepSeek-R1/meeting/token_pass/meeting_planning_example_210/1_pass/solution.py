import itertools
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        'FW': {'P': 17, 'R': 18, 'F': 11},
        'P': {'FW': 19, 'R': 7, 'F': 23},
        'R': {'FW': 18, 'P': 7, 'F': 22},
        'F': {'FW': 10, 'P': 22, 'R': 21}
    }
    
    # People information: location, available start and end (in minutes from 9:00), minimum desired duration
    people_info = {
        'Emily': {'loc': 'P', 'start': 435, 'end': 720, 'min_dur': 105},
        'Joseph': {'loc': 'R', 'start': 495, 'end': 780, 'min_dur': 120},
        'Melissa': {'loc': 'F', 'start': 405, 'end': 765, 'min_dur': 75}
    }
    
    # Generate all non-empty subsets of the locations
    locations = ['P', 'R', 'F']
    all_subsets = []
    for r in range(1, len(locations)+1):
        all_subsets.extend(itertools.permutations(locations, r))
    
    best_meetings = None
    best_score = (-1, -1)  # (number of meetings meeting min duration, total meeting time)
    
    for order in all_subsets:
        current_time = 0  # 9:00 in minutes
        meetings = []
        met_min_count = 0
        total_meeting_time = 0
        
        # Build loc_info from people_info
        loc_info = {}
        for person, info in people_info.items():
            loc_info[info['loc']] = {
                'person': person,
                'start': info['start'],
                'end': info['end'],
                'min_dur': info['min_dur']
            }
        
        for i, loc in enumerate(order):
            info = loc_info[loc]
            # Travel to current location
            if i == 0:
                travel_time = travel_times['FW'][loc]
            else:
                travel_time = travel_times[order[i-1]][loc]
            current_time += travel_time
            
            # Wait if needed
            start_time = max(current_time, info['start'])
            if start_time > info['end']:
                # Cannot meet at all, skip and move to next
                end_time = start_time
                duration = 0
            else:
                if i < len(order) - 1:
                    next_loc = order[i+1]
                    next_info = loc_info[next_loc]
                    travel_to_next = travel_times[loc][next_loc]
                    # Latest departure to meet next minimum
                    latest_departure = (next_info['end'] - next_info['min_dur']) - travel_to_next
                    end_time = min(info['end'], latest_departure)
                    if end_time < start_time:
                        end_time = start_time
                    duration = end_time - start_time
                else:
                    # Last meeting: meet until end of window
                    end_time = info['end']
                    duration = end_time - start_time
                    if duration < info['min_dur']:
                        # Cannot meet minimum, use whatever available
                        end_time = info['end']
                        duration = end_time - start_time
                    else:
                        # Meet at least minimum, but can meet longer
                        end_time = info['end']
                        duration = end_time - start_time
            
            current_time = end_time  # Leave meeting at end_time
            
            if duration > 0:
                meetings.append({
                    'person': info['person'],
                    'location': loc,
                    'start': start_time,
                    'end': end_time,
                    'duration': duration
                })
                if duration >= info['min_dur']:
                    met_min_count += 1
                total_meeting_time += duration
        
        # Update best schedule
        score = (met_min_count, total_meeting_time)
        if score > best_score:
            best_score = score
            best_meetings = meetings
    
    # Convert best_meetings to output format
    itinerary = []
    for meeting in best_meetings:
        start_minutes = meeting['start']
        end_minutes = meeting['end']
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        start_str = f"{start_hour}:{start_minute:02d}"
        end_str = f"{end_hour}:{end_minute:02d}"
        itinerary.append({
            "action": "meet",
            "location": meeting['location'],
            "person": meeting['person'],
            "start_time": start_str,
            "end_time": end_str
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()