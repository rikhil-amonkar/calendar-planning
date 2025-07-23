import itertools
import json

def main():
    travel_times = {
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Financial District'): 19,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Financial District'): 5,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Financial District', 'Bayview'): 19,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Fisherman\'s Wharf'): 10
    }
    
    friends = [
        {
            'name': 'Betty',
            'location': 'Embarcadero',
            'available_start_min': 19 * 60 + 45,
            'available_end_min': 21 * 60 + 45,
            'min_duration_min': 15
        },
        {
            'name': 'Karen',
            'location': 'Fisherman\'s Wharf',
            'available_start_min': 8 * 60 + 45,
            'available_end_min': 15 * 60,
            'min_duration_min': 30
        },
        {
            'name': 'Anthony',
            'location': 'Financial District',
            'available_start_min': 9 * 60 + 15,
            'available_end_min': 21 * 60 + 30,
            'min_duration_min': 105
        }
    ]
    
    start_location = 'Bayview'
    start_time_min = 9 * 60
    
    permutations = list(itertools.permutations(friends))
    best_schedule = None
    
    for perm in permutations:
        current_location = start_location
        current_time = start_time_min
        meetings = []
        total_travel = 0
        
        for friend in perm:
            key = (current_location, friend['location'])
            if key not in travel_times:
                continue
            travel_duration = travel_times[key]
            arrival_time = current_time + travel_duration
            start_meeting = max(arrival_time, friend['available_start_min'])
            if start_meeting > friend['available_end_min'] - friend['min_duration_min']:
                continue
            end_meeting = start_meeting + friend['min_duration_min']
            if end_meeting > friend['available_end_min']:
                continue
            meeting = {
                'person': friend['name'],
                'location': friend['location'],
                'start_time_min': start_meeting,
                'end_time_min': end_meeting
            }
            meetings.append(meeting)
            total_travel += travel_duration
            current_location = friend['location']
            current_time = end_meeting
        
        num_meetings = len(meetings)
        if best_schedule is None:
            best_schedule = (num_meetings, total_travel, meetings)
        else:
            current_best_meetings, current_best_travel = best_schedule[0], best_schedule[1]
            if num_meetings > current_best_meetings:
                best_schedule = (num_meetings, total_travel, meetings)
            elif num_meetings == current_best_meetings and total_travel < current_best_travel:
                best_schedule = (num_meetings, total_travel, meetings)
    
    def min_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    itinerary = []
    if best_schedule and best_schedule[2]:
        for meeting in best_schedule[2]:
            itinerary.append({
                "action": "meet",
                "location": meeting['location'],
                "person": meeting['person'],
                "start_time": min_to_time(meeting['start_time_min']),
                "end_time": min_to_time(meeting['end_time_min'])
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()