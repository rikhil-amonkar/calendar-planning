import json

def main():
    travel_times = {
        'Sunset District': {'Chinatown': 30, 'Russian Hill': 24, 'North Beach': 29},
        'Chinatown': {'Sunset District': 29, 'Russian Hill': 7, 'North Beach': 3},
        'Russian Hill': {'Sunset District': 23, 'Chinatown': 9, 'North Beach': 5},
        'North Beach': {'Sunset District': 27, 'Chinatown': 6, 'Russian Hill': 4}
    }
    
    def format_time(minutes_from_900):
        total_minutes = 9 * 60 + minutes_from_900
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours}:{minutes:02d}"
    
    anthony_start = (13 * 60 + 15) - (9 * 60)
    anthony_end = (14 * 60 + 30) - (9 * 60)
    anthony_min_duration = 60
    
    rebecca_start = (19 * 60 + 30) - (9 * 60)
    rebecca_end = (21 * 60 + 15) - (9 * 60)
    rebecca_min_duration = 105
    
    melissa_start = max(0, (8 * 60 + 15) - (9 * 60))
    melissa_end = (13 * 60 + 30) - (9 * 60)
    melissa_min_duration = 105
    
    arrive_north_beach = travel_times['Sunset District']['North Beach']
    leave_north_beach = min(melissa_end, anthony_end - anthony_min_duration - travel_times['North Beach']['Chinatown'])
    
    arrive_chinatown = leave_north_beach + travel_times['North Beach']['Chinatown']
    anthony_meeting_end = arrive_chinatown + anthony_min_duration
    
    itinerary = [
        {
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": format_time(arrive_north_beach),
            "end_time": format_time(leave_north_beach)
        },
        {
            "action": "meet",
            "location": "Chinatown",
            "person": "Anthony",
            "start_time": format_time(arrive_chinatown),
            "end_time": format_time(anthony_meeting_end)
        },
        {
            "action": "meet",
            "location": "Russian Hill",
            "person": "Rebecca",
            "start_time": format_time(rebecca_start),
            "end_time": format_time(rebecca_start + rebecca_min_duration)
        }
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()