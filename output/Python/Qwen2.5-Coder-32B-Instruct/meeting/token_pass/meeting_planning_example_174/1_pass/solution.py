import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

def can_meet(start, end, available_start, available_end, min_duration):
    return start >= available_start and end <= available_end and (end - start) >= min_duration

def find_optimal_schedule():
    # Constants
    start_time = time_to_minutes("9:00")
    thomas_start = time_to_minutes("15:30")
    thomas_end = time_to_minutes("19:15")
    kenneth_start = time_to_minutes("12:00")
    kenneth_end = time_to_minutes("15:45")
    min_thomas_meeting = 75
    min_kenneth_meeting = 45
    travel_times = {
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Mission District"): 13,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Mission District"): 15,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16
    }
    
    # Possible meeting slots
    thomas_slots = [(thomas_start + i, thomas_start + i + min_thomas_meeting) for i in range(thomas_end - thomas_start - min_thomas_meeting + 1)]
    kenneth_slots = [(kenneth_start + i, kenneth_start + i + min_kenneth_meeting) for i in range(kenneth_end - kenneth_start - min_kenneth_meeting + 1)]
    
    best_schedule = None
    best_meeting_time = 0
    
    # Try all permutations of visiting friends
    for order in permutations(["Thomas", "Kenneth"]):
        for thomas_start, thomas_end in thomas_slots:
            for kenneth_start, kenneth_end in kenneth_slots:
                if order == ("Thomas", "Kenneth"):
                    # Visit Thomas first, then Kenneth
                    if can_meet(thomas_start, thomas_end, thomas_start, thomas_end, min_thomas_meeting):
                        travel_to_kenneth = travel_times[("Pacific Heights", "Mission District")]
                        kenneth_start_time = thomas_end + travel_to_kenneth
                        if can_meet(kenneth_start_time, kenneth_start_time + min_kenneth_meeting, kenneth_start, kenneth_end, min_kenneth_meeting):
                            total_meeting_time = (thomas_end - thomas_start) + (kenneth_start_time + min_kenneth_meeting - kenneth_start_time)
                            if total_meeting_time > best_meeting_time:
                                best_meeting_time = total_meeting_time
                                best_schedule = [
                                    {"action": "meet", "location": "Pacific Heights", "person": "Thomas", "start_time": minutes_to_time(thomas_start), "end_time": minutes_to_time(thomas_end)},
                                    {"action": "meet", "location": "Mission District", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start_time), "end_time": minutes_to_time(kenneth_start_time + min_kenneth_meeting)}
                                ]
                else:
                    # Visit Kenneth first, then Thomas
                    if can_meet(kenneth_start, kenneth_end, kenneth_start, kenneth_end, min_kenneth_meeting):
                        travel_to_thomas = travel_times[("Mission District", "Pacific Heights")]
                        thomas_start_time = kenneth_end + travel_to_thomas
                        if can_meet(thomas_start_time, thomas_start_time + min_thomas_meeting, thomas_start, thomas_end, min_thomas_meeting):
                            total_meeting_time = (kenneth_end - kenneth_start) + (thomas_start_time + min_thomas_meeting - thomas_start_time)
                            if total_meeting_time > best_meeting_time:
                                best_meeting_time = total_meeting_time
                                best_schedule = [
                                    {"action": "meet", "location": "Mission District", "person": "Kenneth", "start_time": minutes_to_time(kenneth_start), "end_time": minutes_to_time(kenneth_end)},
                                    {"action": "meet", "location": "Pacific Heights", "person": "Thomas", "start_time": minutes_to_time(thomas_start_time), "end_time": minutes_to_time(thomas_start_time + min_thomas_meeting)}
                                ]
    
    return best_schedule

# Find and print the optimal schedule
optimal_schedule = find_optimal_schedule()
print(json.dumps({"itinerary": optimal_schedule}, indent=2))