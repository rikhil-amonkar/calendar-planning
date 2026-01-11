import json
from itertools import permutations

def time_to_minutes(t):
    """Convert 'H:MM' string to minutes since midnight."""
    if isinstance(t, str):
        h, m = map(int, t.split(':'))
        return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' string."""
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Travel times in minutes between locations
travel_times = {
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Bayview'): 15,
    ('Union Square', 'Sunset District'): 26,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Sunset District'): 24,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Sunset District'): 22,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Bayview'): 22,
}

# People data: name, location, available start, available end, min_duration
people = [
    ('Rebecca', 'Mission District', time_to_minutes('11:30'), time_to_minutes('20:15'), 120),
    ('Karen', 'Bayview', time_to_minutes('12:45'), time_to_minutes('15:00'), 120),
    ('Carol', 'Sunset District', time_to_minutes('10:15'), time_to_minutes('11:45'), 30),
]

def schedule_meetings(order, start_location='Union Square', start_time=time_to_minutes('9:00')):
    """Try to schedule meetings in given order, return itinerary if possible."""
    current_location = start_location
    current_time = start_time
    itinerary = []
    
    for person_name, location, avail_start, avail_end, min_dur in order:
        # Travel to location
        travel = travel_times.get((current_location, location))
        if travel is None:
            return None  # Should not happen with our locations
        current_time += travel
        
        # Wait if arrived before availability
        if current_time < avail_start:
            current_time = avail_start
        
        # Check if enough time to meet before they leave
        if current_time + min_dur > avail_end:
            return None  # Cannot meet this person
        
        # Schedule meeting
        meeting_end = current_time + min_dur
        itinerary.append({
            'action': 'meet',
            'location': location,
            'person': person_name,
            'start_time': minutes_to_time(current_time),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = location
    
    return itinerary

def main():
    best_itinerary = None
    max_met = 0
    
    # Try all permutations of people (1, 2, or all 3)
    for r in range(1, 4):
        for perm in permutations(people, r):
            itinerary = schedule_meetings(perm)
            if itinerary and len(itinerary) > max_met:
                max_met = len(itinerary)
                best_itinerary = itinerary
    
    # Output result
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()