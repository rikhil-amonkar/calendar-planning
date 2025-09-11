import itertools
import json

def main():
    # Define travel times from the problem (asymmetric)
    travel_pairs = [
        ('Presidio', 'Pacific Heights', 11),
        ('Presidio', 'Golden Gate Park', 12),
        ('Presidio', 'Fisherman\'s Wharf', 19),
        ('Presidio', 'Marina District', 11),
        ('Presidio', 'Alamo Square', 19),
        ('Presidio', 'Sunset District', 15),
        ('Presidio', 'Nob Hill', 18),
        ('Presidio', 'North Beach', 18),
        ('Pacific Heights', 'Presidio', 11),
        ('Pacific Heights', 'Golden Gate Park', 15),
        ('Pacific Heights', 'Fisherman\'s Wharf', 13),
        ('Pacific Heights', 'Marina District', 6),
        ('Pacific Heights', 'Alamo Square', 10),
        ('Pacific Heights', 'Sunset District', 21),
        ('Pacific Heights', 'Nob Hill', 8),
        ('Pacific Heights', 'North Beach', 9),
        ('Golden Gate Park', 'Presidio', 11),
        ('Golden Gate Park', 'Pacific Heights', 16),
        ('Golden Gate Park', 'Fisherman\'s Wharf', 24),
        ('Golden Gate Park', 'Marina District', 16),
        ('Golden Gate Park', 'Alamo Square', 9),
        ('Golden Gate Park', 'Sunset District', 10),
        ('Golden Gate Park', 'Nob Hill', 20),
        ('Golden Gate Park', 'North Beach', 23),
        ('Fisherman\'s Wharf', 'Presidio', 17),
        ('Fisherman\'s Wharf', 'Pacific Heights', 12),
        ('Fisherman\'s Wharf', 'Golden Gate Park', 25),
        ('Fisherman\'s Wharf', 'Marina District', 9),
        ('Fisherman\'s Wharf', 'Alamo Square', 21),
        ('Fisherman\'s Wharf', 'Sunset District', 27),
        ('Fisherman\'s Wharf', 'Nob Hill', 11),
        ('Fisherman\'s Wharf', 'North Beach', 6),
        ('Marina District', 'Presidio', 10),
        ('Marina District', 'Pacific Heights', 7),
        ('Marina District', 'Golden Gate Park', 18),
        ('Marina District', 'Fisherman\'s Wharf', 10),
        ('Marina District', 'Alamo Square', 15),
        ('Marina District', 'Sunset District', 19),
        ('Marina District', 'Nob Hill', 12),
        ('Marina District', 'North Beach', 11),
        ('Alamo Square', 'Presidio', 17),
        ('Alamo Square', 'Pacific Heights', 10),
        ('Alamo Square', 'Golden Gate Park', 9),
        ('Alamo Square', 'Fisherman\'s Wharf', 19),
        ('Alamo Square', 'Marina District', 15),
        ('Alamo Square', 'Sunset District', 16),
        ('Alamo Square', 'Nob Hill', 11),
        ('Alamo Square', 'North Beach', 15),
        ('Sunset District', 'Presidio', 16),
        ('Sunset District', 'Pacific Heights', 21),
        ('Sunset District', 'Golden Gate Park', 11),
        ('Sunset District', 'Fisherman\'s Wharf', 29),
        ('Sunset District', 'Marina District', 21),
        ('Sunset District', 'Alamo Square', 17),
        ('Sunset District', 'Nob Hill', 27),
        ('Sunset District', 'North Beach', 28),
        ('Nob Hill', 'Presidio', 17),
        ('Nob Hill', 'Pacific Heights', 8),
        ('Nob Hill', 'Golden Gate Park', 17),
        ('Nob Hill', 'Fisherman\'s Wharf', 10),
        ('Nob Hill', 'Marina District', 11),
        ('Nob Hill', 'Alamo Square', 11),
        ('Nob Hill', 'Sunset District', 24),
        ('Nob Hill', 'North Beach', 8),
        ('North Beach', 'Presidio', 17),
        ('North Beach', 'Pacific Heights', 8),
        ('North Beach', 'Golden Gate Park', 22),
        ('North Beach', 'Fisherman\'s Wharf', 5),
        ('North Beach', 'Marina District', 9),
        ('North Beach', 'Alamo Square', 16),
        ('North Beach', 'Sunset District', 27),
        ('North Beach', 'Nob Hill', 7)
    ]
    
    # Build travel_times dictionary
    travel_times = {}
    locations = set()
    for from_loc, to_loc, time in travel_pairs:
        locations.add(from_loc)
        locations.add(to_loc)
    for loc in locations:
        travel_times[loc] = {}
    for from_loc, to_loc, time in travel_pairs:
        travel_times[from_loc][to_loc] = time

    # Define friends (excluding Kevin)
    class Friend:
        def __init__(self, name, location, start_str, end_str, min_duration):
            self.name = name
            self.location = location
            self.start = time_to_minutes(start_str)
            self.end = time_to_minutes(end_str)
            self.min_duration = min_duration

    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1][:2])  # Handle AM/PM by ignoring it since we know the times
        if 'PM' in time_str and hour != 12:
            hour += 12
        if 'AM' in time_str and hour == 12:
            hour = 0
        return hour * 60 + minute

    friends = [
        Friend('Michelle', 'Golden Gate Park', '8:00PM', '9:00PM', 15),
        Friend('Emily', 'Fisherman\'s Wharf', '4:15PM', '7:00PM', 30),
        Friend('Mark', 'Marina District', '6:15PM', '7:45PM', 75),
        Friend('Barbara', 'Alamo Square', '5:00PM', '7:00PM', 120),
        Friend('Laura', 'Sunset District', '7:00PM', '9:15PM', 75),
        Friend('Mary', 'Nob Hill', '5:30PM', '7:00PM', 45),
        Friend('Helen', 'North Beach', '11:00AM', '12:15PM', 45)
    ]

    # Start at Presidio at 9:00AM (540 minutes)
    start_time = 540
    start_location = 'Presidio'

    best_count = 0
    best_itinerary = []

    # Generate all permutations of friends
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        for friend in perm:
            # Get travel time to friend's location
            tt = travel_times[current_location][friend.location]
            arrival_time = current_time + tt
            # Meeting can start at arrival or friend's start time, whichever is later
            meeting_start = max(arrival_time, friend.start)
            meeting_end = meeting_start + friend.min_duration
            # Check if meeting fits within friend's availability
            if meeting_end <= friend.end:
                itinerary.append((friend, meeting_start, meeting_end))
                current_time = meeting_end
                current_location = friend.location
        if len(itinerary) > best_count:
            best_count = len(itinerary)
            best_itinerary = itinerary

    # Convert best itinerary to JSON format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    json_itinerary = []
    for meeting in best_itinerary:
        friend, start, end = meeting
        json_itinerary.append({
            "action": "meet",
            "location": friend.location,
            "person": friend.name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

    output = {"itinerary": json_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()