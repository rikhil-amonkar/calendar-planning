#!/usr/bin/env python3
import json
from datetime import datetime, timedelta

# Helper functions for time conversion.
def minutes_to_time_str(minutes_after_9):
    # 9:00 corresponds to 9*60 = 540 minutes in the day.
    total_minutes = 540 + minutes_after_9
    hour = total_minutes // 60
    minute = total_minutes % 60
    # Format without a leading zero in hour part.
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters and constants (all times in minutes relative to 9:00, where 9:00 -> 0)
    # Locations: Bayview (start), Union Square, Presidio
    # Travel times (in minutes):
    travel_Bayview_UnionSquare = 17
    travel_Bayview_Presidio = 31
    travel_UnionSquare_Presidio = 24
    travel_Presidio_UnionSquare = 22

    # Friend constraints.
    # Richard: At Union Square, available 8:45 to 13:00.
    # Convert availability times to minutes relative to 9:00.
    # 8:45 is -15 minutes, 13:00 is 240 minutes.
    richard_avail_start = -15
    richard_avail_end = 240
    richard_min_meeting = 120  # in minutes
    richard_location = "Union Square"

    # Charles: At Presidio, available 9:45 to 13:00.
    charles_avail_start = 45
    charles_avail_end = 240
    charles_min_meeting = 120  # in minutes
    charles_location = "Presidio"

    # We start at Bayview at 9:00 (time=0).
    start_time = 0

    # The goal is to try to meet as many friends as possible meeting their minimum meeting duration.
    # Since travel between locations eats into the day, we check possible itineraries.
    #
    # Option 1: Meet Richard only.
    #
    # - Travel from Bayview to Union Square.
    richard_travel_time = travel_Bayview_UnionSquare
    richard_arrival = start_time + richard_travel_time  # arrival time at Union Square
    # Meeting with Richard can start as soon as arrival, but also not before his availability start.
    richard_meet_start = max(richard_arrival, richard_avail_start)
    richard_meet_end = richard_meet_start + richard_min_meeting
    # Check if meeting ends before Richard's availability.
    richard_possible = (richard_meet_end <= richard_avail_end)

    # Option 2: Meet Charles only.
    charles_travel_time = travel_Bayview_Presidio
    charles_arrival = start_time + charles_travel_time  # arrival at Presidio
    charles_meet_start = max(charles_arrival, charles_avail_start)
    charles_meet_end = charles_meet_start + charles_min_meeting
    charles_possible = (charles_meet_end <= charles_avail_end)

    # Option 3: Try to meet both by splitting the day into two segments.
    # We will attempt two possible sequences:
    # Sequence A: Meet Richard first (at Union Square) then travel to Presidio for Charles.
    # Sequence B: Meet Charles first (at Presidio) then travel to Union Square for Richard.
    #
    # For a meeting to count, the total meeting time with that friend (even if split) must be at least the minimum.
    # We assume that the meeting segments must occur at the designated location and cannot overlap travel.
    #
    # Sequence A: Bayview -> Union Square -> Presidio.
    # Let r1 be the time spent meeting Richard at Union Square in the first segment.
    # After that, travel from Union Square to Presidio takes travel_UnionSquare_Presidio minutes.
    # Then, meet Charles continuously.
    # In this route, Richard would only get one segment and must have at least 120 minutes.
    # Total time needed: travel (Bayview->UnionSquare) + r1 + travel (UnionSquare->Presidio) + charles_min_meeting.
    r1 = richard_min_meeting  # Must be at least 120 minutes.
    seqA_start_richard = max(start_time + travel_Bayview_UnionSquare, richard_avail_start)
    seqA_end_richard = seqA_start_richard + r1
    seqA_arrival_presidio = seqA_end_richard + travel_UnionSquare_Presidio
    # Meeting with Charles would then start at max(seqA_arrival_presidio, charles_avail_start)
    seqA_start_charles = max(seqA_arrival_presidio, charles_avail_start)
    seqA_end_charles = seqA_start_charles + charles_min_meeting
    seqA_possible = (seqA_end_charles <= charles_avail_end) and (seqA_start_richard >= start_time)
    # For r1 =120, check timing:
    # Richard: arrives at Union Square at time = 0+17 = 17, so meeting from 17 to 137.
    # Then travel to Presidio takes 24 minutes: arrive at 161.
    # Then meeting Charles from max(161,45)=161 to 161+120 = 281, but 281 > 240.
    # So sequence A is not possible.
    
    # Sequence B: Bayview -> Presidio -> Union Square.
    # In this sequence, we meet Charles first and then Richard.
    # Charles meeting must be at least 120 minutes.
    # Bayview to Presidio travel time: 31.
    # Wait until charles_avail_start if arrived early.
    # Let c1 = charles_min_meeting =120.
    # Then travel from Presidio to Union Square takes travel_Presidio_UnionSquare minutes.
    # Then meeting Richard continuously for 120 minutes.
    seqB_start_charles = max(start_time + travel_Bayview_Presidio, charles_avail_start)
    seqB_end_charles = seqB_start_charles + charles_min_meeting
    seqB_arrival_union = seqB_end_charles + travel_Presidio_UnionSquare
    seqB_start_richard = max(seqB_arrival_union, richard_avail_start)
    seqB_end_richard = seqB_start_richard + richard_min_meeting
    seqB_possible = (seqB_end_richard <= richard_avail_end)
    # For sequence B:
    # Arrival at Presidio = 0+31 = 31, but must wait until 45, so start Charles meeting at 45, end at 165.
    # Then travel to Union Square: 165 + 22 = 187, start Richard meeting at 187, end at 187+120 = 307.
    # 307 is beyond Richard's available end (240). So sequence B is not possible either.
    
    # Thus, it is impossible to schedule both meetings with the required minimum meeting durations.
    # We choose the option that meets the maximum number of friends' minimum meeting duration.
    # Both Option 1 (Richard only) and Option 2 (Charles only) are individually possible.
    # As a tie-breaker, we choose the itinerary with lower travel time (i.e. less overall commitment).
    if richard_possible and charles_possible:
        if travel_Bayview_UnionSquare <= travel_Bayview_Presidio:
            chosen_option = "Richard"
        else:
            chosen_option = "Charles"
    elif richard_possible:
        chosen_option = "Richard"
    elif charles_possible:
        chosen_option = "Charles"
    else:
        chosen_option = None  # No feasible itinerary

    itinerary = []
    
    if chosen_option == "Richard":
        # Travel from Bayview to Union Square (implicitly, meeting starts after travel)
        meeting_start = max(start_time + travel_Bayview_UnionSquare, richard_avail_start)
        meeting_end = meeting_start + richard_min_meeting
        # Build meeting entry.
        meeting_entry = {
            "action": "meet",
            "location": richard_location,
            "person": "Richard",
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
        itinerary.append(meeting_entry)
    elif chosen_option == "Charles":
        meeting_start = max(start_time + travel_Bayview_Presidio, charles_avail_start)
        meeting_end = meeting_start + charles_min_meeting
        meeting_entry = {
            "action": "meet",
            "location": charles_location,
            "person": "Charles",
            "start_time": minutes_to_time_str(meeting_start),
            "end_time": minutes_to_time_str(meeting_end)
        }
        itinerary.append(meeting_entry)
    else:
        # In case no itinerary meets the requirements.
        itinerary = []

    result = {"itinerary": itinerary}
    # Output the JSON result.
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()