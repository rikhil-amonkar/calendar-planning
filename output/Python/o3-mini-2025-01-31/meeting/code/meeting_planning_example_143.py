#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper function to format time in H:MM with no leading zero for hour
def format_time(dt):
    return f"{dt.hour}:{dt.minute:02d}"

def main():
    # Input parameters & constraints
    # Arrival time at North Beach: 9:00 AM (use an arbitrary date)
    base_date = datetime(2023, 1, 1)  # arbitrary date; only time matters
    arrival_north_beach = base_date.replace(hour=9, minute=0)
    
    # Travel times (in minutes) between locations
    travel_times = {
        'North Beach': {'Pacific Heights': 8, 'Embarcadero': 6},
        'Pacific Heights': {'North Beach': 9, 'Embarcadero': 10},
        'Embarcadero': {'North Beach': 5, 'Pacific Heights': 11}
    }
    
    # Meeting constraints
    # Karen: at Pacific Heights from 18:45 to 20:15, needs at least 90 minutes meeting
    karen_location = "Pacific Heights"
    karen_avail_start = base_date.replace(hour=18, minute=45)
    karen_avail_end   = base_date.replace(hour=20, minute=15)
    karen_min_duration = timedelta(minutes=90)
    
    # Mark: at Embarcadero from 13:00 to 17:45, needs at least 120 minutes meeting
    mark_location = "Embarcadero"
    mark_avail_start = base_date.replace(hour=13, minute=0)
    mark_avail_end   = base_date.replace(hour=17, minute=45)
    mark_min_duration = timedelta(minutes=120)
    
    # We start at North Beach. Our plan is to meet Mark first at Embarcadero
    # Compute the departure time from North Beach to be on time for Mark's availability.
    travel_nb_to_em = timedelta(minutes=travel_times['North Beach']['Embarcadero'])
    # We want to arrive at Mark's location at mark_avail_start, so departure_time = mark_avail_start - travel_time.
    departure_from_nb = mark_avail_start - travel_nb_to_em
    
    # Check if we're at North Beach long enough (we arrive at 9:00).
    if arrival_north_beach > departure_from_nb:
        raise Exception("Not enough time at North Beach before departing to Mark.")
    
    # Set Mark meeting schedule.
    # We need a minimum of 120 minutes meeting within the availability window.
    # We can maximize the meeting duration by scheduling it as late as possible
    # but for simplicity, we set the meeting to begin exactly at mark_avail_start and end at mark_avail_end
    # which is a duration of 4 hours 45 minutes (>=120 minutes).
    mark_meet_start = mark_avail_start
    mark_meet_end = mark_avail_end  # Use the full available window to ensure the minimum is met
    
    # After meeting Mark, travel from Embarcadero to Pacific Heights for Karen
    travel_em_to_ph = timedelta(minutes=travel_times['Embarcadero']['Pacific Heights'])
    departure_from_em = mark_meet_end
    arrival_at_ph = departure_from_em + travel_em_to_ph
    
    # Karen is available starting at 18:45; if we arrive early, wait until then.
    if arrival_at_ph < karen_avail_start:
        karen_meet_start = karen_avail_start
    else:
        karen_meet_start = arrival_at_ph
    
    # Now schedule Karen meeting: The required minimum meeting duration is 90 minutes.
    # We choose the meeting end as karen_meet_start + 90 minutes.
    karen_meet_end = karen_meet_start + karen_min_duration
    
    # Check if Karen's meeting falls within her availability window.
    if karen_meet_end > karen_avail_end:
        # If our computed meeting goes beyond available time, adjust to use her entire available window.
        karen_meet_start = karen_avail_start
        karen_meet_end = karen_avail_end
        # And we assume that this still meets the minimum requirement.
        if (karen_meet_end - karen_meet_start) < karen_min_duration:
            raise Exception("Karen's available window does not meet the minimum meeting duration.")
    
    # Construct itinerary of meeting events (only meetings as required)
    itinerary = []
    itinerary.append({
        "action": "meet",
        "location": mark_location,
        "person": "Mark",
        "start_time": format_time(mark_meet_start),
        "end_time": format_time(mark_meet_end)
    })
    itinerary.append({
        "action": "meet",
        "location": karen_location,
        "person": "Karen",
        "start_time": format_time(karen_meet_start),
        "end_time": format_time(karen_meet_end)
    })
    
    # Final output in JSON format.
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()