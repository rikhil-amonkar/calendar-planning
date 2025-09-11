import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def generate_schedule(perm, travel_times):
    current_time = 540  # 9:00 AM
    current_location = 'Haight-Ashbury'
    schedule = []
    for friend in perm:
        loc = friend['location']
        available_start = friend['available_start']
        available_end = friend['available_end']
        required = friend['required']
        travel_time = travel_times[(current_location, loc)]
        arrival_time = current_time + travel_time
        earliest_start = max(arrival_time, available_start)
        latest_start = available_end - required
        if earliest_start > latest_start:
            return None
        meeting_start = earliest_start
        meeting_end = meeting_start + required
        schedule.append({
            'action': 'meet',
            'location': loc,
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        })
        current_time = meeting_end
        current_location = loc
    return schedule

friends = [
    {
        'name': 'Stephanie',
        'location': 'Mission District',
        'available_start': 8*60 + 15,  # 495
        'available_end': 13*60 + 45,   # 805
        'required': 90
    },
    {
        'name': 'Jason',
        'location': "Fisherman's Wharf",
        'available_start': 8*60 + 30,  # 510
        'available_end': 17*60 + 45,   # 1065
        'required': 60
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'available_start': 12*60 + 15,  # 735
        'available_end': 16*60 + 0,     # 960
        'required': 120
    },
    {
        'name': 'Sandra',
        'location': 'Bayview',
        'available_start': 13*60 + 0,   # 780
        'available_end': 19*60 + 30,    # 1170
        'required': 15
    },
]

travel_times = {
    # From Haight-Ashbury
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', "Fisherman's Wharf"): 23,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    # From Mission District
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', "Fisherman's Wharf"): 22,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Russian Hill'): 15,
    # From Bayview
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', "Fisherman's Wharf"): 25,
    # From Pacific Heights
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Bayview'): 22,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', "Fisherman's Wharf"): 13,
    # From Russian Hill
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', "Fisherman's Wharf"): 7,
    # From Fisherman's Wharf
    ("Fisherman's Wharf", 'Haight-Ashbury'): 22,
    ("Fisherman's Wharf", 'Mission District'): 22,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Pacific Heights'): 12,
    ("Fisherman's Wharf", 'Russian Hill'): 7,
}

for subset_size in range(4, 0, -1):
    for perm in itertools.permutations(friends, subset_size):
        schedule = generate_schedule(perm, travel_times)
        if schedule:
            output = {
                "itinerary": schedule
            }
            print(json.dumps(output, indent=2))
            exit()

print(json.dumps({"itinerary": []}))