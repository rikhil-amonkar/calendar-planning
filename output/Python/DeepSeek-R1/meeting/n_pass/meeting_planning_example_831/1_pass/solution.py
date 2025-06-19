import json

def main():
    # Define travel_times dictionary
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19,
            "Alamo Square": 19,
            "Financial District": 23,
            "Union Square": 22,
            "Sunset District": 15,
            "Embarcadero": 20,
            "Golden Gate Park": 12,
            "Chinatown": 21,
            "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17,
            "Alamo Square": 21,
            "Financial District": 11,
            "Union Square": 13,
            "Sunset District": 27,
            "Embarcadero": 8,
            "Golden Gate Park": 25,
            "Chinatown": 12,
            "Richmond District": 18
        },
        "Alamo Square": {
            "Presidio": 17,
            "Fisherman's Wharf": 19,
            "Financial District": 17,
            "Union Square": 14,
            "Sunset District": 16,
            "Embarcadero": 16,
            "Golden Gate Park": 9,
            "Chinatown": 15,
            "Richmond District": 11
        },
        "Financial District": {
            "Presidio": 22,
            "Fisherman's Wharf": 10,
            "Alamo Square": 17,
            "Union Square": 9,
            "Sunset District": 30,
            "Embarcadero": 4,
            "Golden Gate Park": 23,
            "Chinatown": 5,
            "Richmond District": 21
        },
        "Union Square": {
            "Presidio": 24,
            "Fisherman's Wharf": 15,
            "Alamo Square": 15,
            "Financial District": 9,
            "Sunset District": 27,
            "Embarcadero": 11,
            "Golden Gate Park": 22,
            "Chinatown": 7,
            "Richmond District": 20
        },
        "Sunset District": {
            "Presidio": 16,
            "Fisherman's Wharf": 29,
            "Alamo Square": 17,
            "Financial District": 30,
            "Union Square": 30,
            "Embarcadero": 30,
            "Golden Gate Park": 11,
            "Chinatown": 30,
            "Richmond District": 12
        },
        "Embarcadero": {
            "Presidio": 20,
            "Fisherman's Wharf": 6,
            "Alamo Square": 19,
            "Financial District": 5,
            "Union Square": 10,
            "Sunset District": 30,
            "Golden Gate Park": 25,
            "Chinatown": 7,
            "Richmond District": 21
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Fisherman's Wharf": 24,
            "Alamo Square": 9,
            "Financial District": 26,
            "Union Square": 22,
            "Sunset District": 10,
            "Embarcadero": 25,
            "Chinatown": 23,
            "Richmond District": 7
        },
        "Chinatown": {
            "Presidio": 19,
            "Fisherman's Wharf": 8,
            "Alamo Square": 17,
            "Financial District": 5,
            "Union Square": 7,
            "Sunset District": 29,
            "Embarcadero": 5,
            "Golden Gate Park": 23,
            "Richmond District": 20
        },
        "Richmond District": {
            "Presidio": 7,
            "Fisherman's Wharf": 18,
            "Alamo Square": 13,
            "Financial District": 22,
            "Union Square": 21,
            "Sunset District": 11,
            "Embarcadero": 19,
            "Golden Gate Park": 9,
            "Chinatown": 20
        }
    }
    
    # Add self-travel as 0
    locations = list(travel_times.keys())
    for loc in locations:
        travel_times[loc][loc] = 0

    # Helper function to convert time string to minutes since 9:00
    def time_str_to_minutes_since_900(time_str):
        time_str = time_str.strip()
        am_pm = time_str[-2:]
        time_part = time_str[:-2].strip()
        parts = time_part.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        if am_pm == "PM" and hour != 12:
            hour += 12
        elif am_pm == "AM" and hour == 12:
            hour = 0
        total_minutes_since_midnight = hour * 60 + minute
        return total_minutes_since_midnight - 540  # 9:00 is 540 minutes from midnight

    # Define friends with converted times
    friends = [
        {'name': 'Jeffrey', 'location': "Fisherman's Wharf", 
         'start_avail': time_str_to_minutes_since_900("10:15AM"), 
         'end_avail': time_str_to_minutes_since_900("1:00PM"), 
         'min_duration': 90},
        {'name': 'Ronald', 'location': "Alamo Square", 
         'start_avail': time_str_to_minutes_since_900("7:45AM"), 
         'end_avail': time_str_to_minutes_since_900("2:45PM"), 
         'min_duration': 120},
        {'name': 'Jason', 'location': "Financial District", 
         'start_avail': time_str_to_minutes_since_900("10:45AM"), 
         'end_avail': time_str_to_minutes_since_900("4:00PM"), 
         'min_duration': 105},
        {'name': 'Melissa', 'location': "Union Square", 
         'start_avail': time_str_to_minutes_since_900("5:45PM"), 
         'end_avail': time_str_to_minutes_since_900("6:15PM"), 
         'min_duration': 15},
        {'name': 'Elizabeth', 'location': "Sunset District", 
         'start_avail': time_str_to_minutes_since_900("2:45PM"), 
         'end_avail': time_str_to_minutes_since_900("5:30PM"), 
         'min_duration': 105},
        {'name': 'Margaret', 'location': "Embarcadero", 
         'start_avail': time_str_to_minutes_since_900("1:15PM"), 
         'end_avail': time_str_to_minutes_since_900("7:00PM"), 
         'min_duration': 90},
        {'name': 'George', 'location': "Golden Gate Park", 
         'start_avail': time_str_to_minutes_since_900("7:00PM"), 
         'end_avail': time_str_to_minutes_since_900("10:00PM"), 
         'min_duration': 75},
        {'name': 'Richard', 'location': "Chinatown", 
         'start_avail': time_str_to_minutes_since_900("9:30AM"), 
         'end_avail': time_str_to_minutes_since_900("9:00PM"), 
         'min_duration': 15},
        {'name': 'Laura', 'location': "Richmond District", 
         'start_avail': time_str_to_minutes_since_900("9:45AM"), 
         'end_avail': time_str_to_minutes_since_900("6:00PM"), 
         'min_duration': 60}
    ]

    # Helper function to convert minutes since 9:00 to time string
    def minutes_to_time(minutes_since_900):
        total_minutes = minutes_since_900 + 540
        hour = total_minutes // 60
        minute = total_minutes % 60
        return f"{hour}:{minute:02d}"

    # DFS with memoization to find optimal schedule
    memo = {}
    
    def dfs(current_time, current_location, visited):
        state_key = (current_location, frozenset(visited))
        if state_key in memo and memo[state_key] <= current_time:
            return []
        memo[state_key] = current_time
        
        best_schedule = []
        for i, friend in enumerate(friends):
            if i in visited:
                continue
            loc = friend['location']
            travel_time = travel_times[current_location][loc]
            arrival_time = current_time + travel_time
            start_meeting = max(arrival_time, friend['start_avail'])
            end_meeting = start_meeting + friend['min_duration']
            
            if end_meeting <= friend['end_avail']:
                new_visited = visited | {i}
                future_schedule = dfs(end_meeting, loc, new_visited)
                candidate_schedule = [(i, start_meeting, end_meeting)] + future_schedule
                if len(candidate_schedule) > len(best_schedule):
                    best_schedule = candidate_schedule
        return best_schedule

    # Start DFS from Presidio at 9:00 (0 minutes since 9:00)
    start_time = 0
    start_location = "Presidio"
    visited = set()
    schedule = dfs(start_time, start_location, visited)
    
    # Build itinerary
    itinerary = []
    for meeting in schedule:
        i, start_minutes, end_minutes = meeting
        friend = friends[i]
        start_time_str = minutes_to_time(start_minutes)
        end_time_str = minutes_to_time(end_minutes)
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_time_str,
            "end_time": end_time_str
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()