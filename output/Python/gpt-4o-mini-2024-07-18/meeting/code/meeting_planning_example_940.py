import json
from datetime import datetime, timedelta

# Define travel distances (in minutes) between locations
travel_times = {
    ("Union Square", "Mission District"): 14,
    ("Union Square", "Fisherman's Wharf"): 15,
    ("Union Square", "Russian Hill"): 13,
    ("Union Square", "Marina District"): 18,
    ("Union Square", "North Beach"): 10,
    ("Union Square", "Chinatown"): 7,
    ("Union Square", "Pacific Heights"): 15,
    ("Union Square", "The Castro"): 17,
    ("Union Square", "Nob Hill"): 9,
    ("Union Square", "Sunset District"): 27,
    ("Mission District", "Union Square"): 15,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Russian Hill"): 15,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "North Beach"): 17,
    ("Mission District", "Chinatown"): 16,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Nob Hill"): 12,
    ("Mission District", "Sunset District"): 24,
    ("Fisherman's Wharf", "Union Square"): 13,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Russian Hill"): 7,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "North Beach"): 6,
    ("Fisherman's Wharf", "Chinatown"): 12,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Nob Hill"): 11,
    ("Fisherman's Wharf", "Sunset District"): 27,
    ("Russian Hill", "Union Square"): 10,
    ("Russian Hill", "Mission District"): 16,
    ("Russian Hill", "Fisherman's Wharf"): 7,
    ("Russian Hill", "Marina District"): 7,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Chinatown"): 9,
    ("Russian Hill", "Pacific Heights"): 7,
    ("Russian Hill", "The Castro"): 21,
    ("Russian Hill", "Nob Hill"): 5,
    ("Russian Hill", "Sunset District"): 23,
    ("Marina District", "Union Square"): 16,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Russian Hill"): 8,
    ("Marina District", "North Beach"): 11,
    ("Marina District", "Chinatown"): 15,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Nob Hill"): 12,
    ("Marina District", "Sunset District"): 19,
    ("North Beach", "Union Square"): 7,
    ("North Beach", "Mission District"): 18,
    ("North Beach", "Fisherman's Wharf"): 5,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Marina District"): 9,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Pacific Heights"): 8,
    ("North Beach", "The Castro"): 23,
    ("North Beach", "Nob Hill"): 7,
    ("North Beach", "Sunset District"): 27,
    ("Chinatown", "Union Square"): 7,
    ("Chinatown", "Mission District"): 17,
    ("Chinatown", "Fisherman's Wharf"): 8,
    ("Chinatown", "Russian Hill"): 7,
    ("Chinatown", "Marina District"): 12,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Pacific Heights"): 10,
    ("Chinatown", "The Castro"): 22,
    ("Chinatown", "Nob Hill"): 9,
    ("Chinatown", "Sunset District"): 29,
    ("Pacific Heights", "Union Square"): 12,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Russian Hill"): 7,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "North Beach"): 9,
    ("Pacific Heights", "Chinatown"): 11,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Nob Hill"): 8,
    ("Pacific Heights", "Sunset District"): 21,
    ("The Castro", "Union Square"): 19,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Russian Hill"): 18,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "North Beach"): 20,
    ("The Castro", "Chinatown"): 22,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Nob Hill"): 16,
    ("The Castro", "Sunset District"): 17,
    ("Nob Hill", "Union Square"): 7,
    ("Nob Hill", "Mission District"): 13,
    ("Nob Hill", "Fisherman's Wharf"): 10,
    ("Nob Hill", "Russian Hill"): 5,
    ("Nob Hill", "Marina District"): 11,
    ("Nob Hill", "North Beach"): 8,
    ("Nob Hill", "Chinatown"): 6,
    ("Nob Hill", "Pacific Heights"): 8,
    ("Nob Hill", "The Castro"): 17,
    ("Nob Hill", "Sunset District"): 24,
    ("Sunset District", "Union Square"): 30,
    ("Sunset District", "Mission District"): 25,
    ("Sunset District", "Fisherman's Wharf"): 29,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Marina District"): 21,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Pacific Heights"): 21,
    ("Sunset District", "The Castro"): 17,
    ("Sunset District", "Nob Hill"): 27,
}

# Meeting constraints for each person
meetings = [
    {"name": "Kevin", "location": "Mission District", "start": "21:45", "end": "22:45", "duration": 60},
    {"name": "Mark", "location": "Fisherman's Wharf", "start": "17:15", "end": "20:00", "duration": 90},
    {"name": "Jessica", "location": "Russian Hill", "start": "09:00", "end": "15:00", "duration": 120},
    {"name": "Jason", "location": "Marina District", "start": "15:15", "end": "21:45", "duration": 120},
    {"name": "John", "location": "North Beach", "start": "09:45", "end": "18:00", "duration": 15},
    {"name": "Karen", "location": "Chinatown", "start": "16:45", "end": "19:00", "duration": 75},
    {"name": "Sarah", "location": "Pacific Heights", "start": "17:30", "end": "18:15", "duration": 45},
    {"name": "Amanda", "location": "The Castro", "start": "20:00", "end": "21:15", "duration": 60},
    {"name": "Nancy", "location": "Nob Hill", "start": "09:45", "end": "13:00", "duration": 45},
    {"name": "Rebecca", "location": "Sunset District", "start": "08:45", "end": "15:00", "duration": 75},
]

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def find_optimal_meeting_schedule():
    itinerary = []
    current_time = parse_time("09:00")
    
    # Meeting with Jessica at Russian Hill
    if current_time < parse_time("15:00"):
        j_start = max(current_time + timedelta(minutes=travel_times[("Union Square", "Russian Hill")]), parse_time("09:00"))
        j_end = j_start + timedelta(minutes=120) 
        itinerary.append({"action": "meet", "location": "Russian Hill", "person": "Jessica", "start_time": format_time(j_start), "end_time": format_time(j_end)})
        current_time = j_end + timedelta(minutes=travel_times[("Russian Hill", "Marina District")]) # travel to Marina District

    # Meeting with Jason at Marina District
    if current_time < parse_time("21:45"):
        j_start = max(current_time, parse_time("15:15"))
        j_end = j_start + timedelta(minutes=120)
        itinerary.append({"action": "meet", "location": "Marina District", "person": "Jason", "start_time": format_time(j_start), "end_time": format_time(j_end)})
        current_time = j_end + timedelta(minutes=travel_times[("Marina District", "Fisherman's Wharf")]) # travel to Fisherman's Wharf

    # Meeting with Mark at Fisherman's Wharf
    if current_time < parse_time("20:00"):
        m_start = max(current_time, parse_time("17:15"))
        m_end = m_start + timedelta(minutes=90)
        itinerary.append({"action": "meet", "location": "Fisherman's Wharf", "person": "Mark", "start_time": format_time(m_start), "end_time": format_time(m_end)})
        current_time = m_end + timedelta(minutes=travel_times[("Fisherman's Wharf", "Mission District")]) # travel to Mission District

    # Meeting with Kevin at Mission District
    if current_time < parse_time("22:45"):
        k_start = max(current_time, parse_time("21:45"))
        k_end = k_start + timedelta(minutes=60)
        itinerary.append({"action": "meet", "location": "Mission District", "person": "Kevin", "start_time": format_time(k_start), "end_time": format_time(k_end)})
        
    # Meeting with John at North Beach
    if current_time < parse_time("18:00"):
        j_start = max(current_time, parse_time("09:45"))
        j_end = j_start + timedelta(minutes=15)
        itinerary.append({"action": "meet", "location": "North Beach", "person": "John", "start_time": format_time(j_start), "end_time": format_time(j_end)})
        current_time = j_end + timedelta(minutes=travel_times[("North Beach", "Chinatown")]) # travel to Chinatown

    # Meeting with Karen at Chinatown
    if current_time < parse_time("19:00"):
        k_start = max(current_time, parse_time("16:45"))
        k_end = k_start + timedelta(minutes=75)
        itinerary.append({"action": "meet", "location": "Chinatown", "person": "Karen", "start_time": format_time(k_start), "end_time": format_time(k_end)})
        current_time = k_end + timedelta(minutes=travel_times[("Chinatown", "Pacifc Heights")]) # travel to Pacific Heights

    # Meeting with Sarah at Pacific Heights
    if current_time < parse_time("18:15"):
        s_start = max(current_time, parse_time("17:30"))
        s_end = s_start + timedelta(minutes=45)
        itinerary.append({"action": "meet", "location": "Pacific Heights", "person": "Sarah", "start_time": format_time(s_start), "end_time": format_time(s_end)})
        current_time = s_end + timedelta(minutes=travel_times[("Pacific Heights", "The Castro")]) # travel to The Castro

    # Meeting with Amanda at The Castro
    if current_time < parse_time("21:15"):
        a_start = max(current_time, parse_time("20:00"))
        a_end = a_start + timedelta(minutes=60)
        itinerary.append({"action": "meet", "location": "The Castro", "person": "Amanda", "start_time": format_time(a_start), "end_time": format_time(a_end)})

    # Meeting with Nancy at Nob Hill
    if current_time < parse_time("13:00"):
        n_start = max(current_time, parse_time("09:45"))
        n_end = n_start + timedelta(minutes=45)
        itinerary.append({"action": "meet", "location": "Nob Hill", "person": "Nancy", "start_time": format_time(n_start), "end_time": format_time(n_end)})
        current_time = n_end + timedelta(minutes=travel_times[("Nob Hill", "Union Square")]) # travel to Union Square

    # Meeting with Rebecca at Sunset District
    if current_time < parse_time("15:00"):
        r_start = max(current_time, parse_time("08:45"))
        r_end = r_start + timedelta(minutes=75)
        itinerary.append({"action": "meet", "location": "Sunset District", "person": "Rebecca", "start_time": format_time(r_start), "end_time": format_time(r_end)})

    return {"itinerary": itinerary}

optimal_schedule = find_optimal_meeting_schedule()

# Outputting the result as JSON
print(json.dumps(optimal_schedule, indent=2))