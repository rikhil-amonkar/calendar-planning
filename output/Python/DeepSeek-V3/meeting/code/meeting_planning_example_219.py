import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%I:%M%p')

def format_time(dt):
    return dt.strftime('%H:%M')

def compute_schedule():
    # Initialize locations and travel times
    locations = ['The Castro', 'Alamo Square', 'Union Square', 'Chinatown']
    travel_times = {
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'Chinatown'): 20,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'Chinatown'): 16,
        ('Union Square', 'The Castro'): 19,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Union Square'): 7,
    }

    # Parse constraints
    current_time = parse_time('9:00AM')
    current_location = 'The Castro'

    emily_available_start = parse_time('11:45AM')
    emily_available_end = parse_time('3:15PM')
    emily_min_duration = timedelta(minutes=105)

    barbara_available_start = parse_time('4:45PM')
    barbara_available_end = parse_time('6:15PM')
    barbara_min_duration = timedelta(minutes=60)

    william_available_start = parse_time('5:15PM')
    william_available_end = parse_time('7:00PM')
    william_min_duration = timedelta(minutes=105)

    itinerary = []

    # Try to meet Emily first
    travel_to_alamo = travel_times[(current_location, 'Alamo Square')]
    arrival_alamo = current_time + timedelta(minutes=travel_to_alamo)
    if arrival_alamo <= emily_available_end - emily_min_duration:
        meet_emily_start = max(arrival_alamo, emily_available_start)
        meet_emily_end = meet_emily_start + emily_min_duration
        if meet_emily_end <= emily_available_end:
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "Emily",
                "start_time": format_time(meet_emily_start),
                "end_time": format_time(meet_emily_end)
            })
            current_time = meet_emily_end
            current_location = 'Alamo Square'

    # Now try to meet Barbara and William
    # First option: meet Barbara then William
    option1 = []
    travel_to_union = travel_times[(current_location, 'Union Square')]
    arrival_union = current_time + timedelta(minutes=travel_to_union)
    if arrival_union <= barbara_available_end - barbara_min_duration:
        meet_barbara_start = max(arrival_union, barbara_available_start)
        meet_barbara_end = meet_barbara_start + barbara_min_duration
        if meet_barbara_end <= barbara_available_end:
            option1.append({
                "action": "meet",
                "location": "Union Square",
                "person": "Barbara",
                "start_time": format_time(meet_barbara_start),
                "end_time": format_time(meet_barbara_end)
            })
            travel_to_chinatown = travel_times[('Union Square', 'Chinatown')]
            arrival_chinatown = meet_barbara_end + timedelta(minutes=travel_to_chinatown)
            if arrival_chinatown <= william_available_end - william_min_duration:
                meet_william_start = max(arrival_chinatown, william_available_start)
                meet_william_end = meet_william_start + william_min_duration
                if meet_william_end <= william_available_end:
                    option1.append({
                        "action": "meet",
                        "location": "Chinatown",
                        "person": "William",
                        "start_time": format_time(meet_william_start),
                        "end_time": format_time(meet_william_end)
                    })

    # Second option: meet William then Barbara
    option2 = []
    travel_to_chinatown = travel_times[(current_location, 'Chinatown')]
    arrival_chinatown = current_time + timedelta(minutes=travel_to_chinatown)
    if arrival_chinatown <= william_available_end - william_min_duration:
        meet_william_start = max(arrival_chinatown, william_available_start)
        meet_william_end = meet_william_start + william_min_duration
        if meet_william_end <= william_available_end:
            option2.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "William",
                "start_time": format_time(meet_william_start),
                "end_time": format_time(meet_william_end)
            })
            travel_to_union = travel_times[('Chinatown', 'Union Square')]
            arrival_union = meet_william_end + timedelta(minutes=travel_to_union)
            if arrival_union <= barbara_available_end - barbara_min_duration:
                meet_barbara_start = max(arrival_union, barbara_available_start)
                meet_barbara_end = meet_barbara_start + barbara_min_duration
                if meet_barbara_end <= barbara_available_end:
                    option2.append({
                        "action": "meet",
                        "location": "Union Square",
                        "person": "Barbara",
                        "start_time": format_time(meet_barbara_start),
                        "end_time": format_time(meet_barbara_end)
                    })

    # Choose the best option
    if len(option1) == 2:
        itinerary.extend(option1)
    elif len(option2) == 2:
        itinerary.extend(option2)
    else:
        # Try to meet at least one person
        if len(option1) >= len(option2):
            itinerary.extend(option1)
        else:
            itinerary.extend(option2)

    return {"itinerary": itinerary}

result = compute_schedule()
print(json.dumps(result, indent=2))