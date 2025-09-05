#!/usr/bin/env python3
import json

def minutes_to_time(minutes):
    """Convert minutes since midnight to H:MM format (24-hour) with no leading zero for hour."""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02}"

def main():
    # Travel times (in minutes)
    travel_times = {
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Presidio"): 31,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Presidio"): 24,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Union Square"): 22
    }

    # Arrival time at Bayview: 9:00AM expressed in minutes since midnight
    bayview_arrival = 9 * 60  # 540

    # Friend constraints:
    # Richard is at Union Square from 8:45AM to 13:00 (525 to 780 minutes) and requires 120 minutes meeting.
    richard_location = "Union Square"
    richard_avail_start = 8 * 60 + 45  # 525
    richard_avail_end = 13 * 60        # 780
    richard_min = 120

    # Charles is at Presidio from 9:45AM to 13:00 (585 to 780 minutes) and requires 120 minutes meeting.
    charles_location = "Presidio"
    charles_avail_start = 9 * 60 + 45  # 585
    charles_avail_end = 13 * 60        # 780
    charles_min = 120

    candidates = []

    # Candidate 1: Meet Richard only.
    travel_to_richard = travel_times[("Bayview", richard_location)]
    arrival_richard = bayview_arrival + travel_to_richard
    meeting_start_richard = max(arrival_richard, richard_avail_start)
    meeting_end_richard = meeting_start_richard + richard_min
    if meeting_end_richard <= richard_avail_end:
        candidate_richard = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": richard_location,
                    "person": "Richard",
                    "start_time": minutes_to_time(meeting_start_richard),
                    "end_time": minutes_to_time(meeting_end_richard)
                }
            ],
            "friends_met": 1,
            "finish_time": meeting_end_richard,
            "total_travel_time": travel_to_richard
        }
        candidates.append(candidate_richard)

    # Candidate 2: Meet Charles only.
    travel_to_charles = travel_times[("Bayview", charles_location)]
    arrival_charles = bayview_arrival + travel_to_charles
    meeting_start_charles = max(arrival_charles, charles_avail_start)
    meeting_end_charles = meeting_start_charles + charles_min
    if meeting_end_charles <= charles_avail_end:
        candidate_charles = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": charles_location,
                    "person": "Charles",
                    "start_time": minutes_to_time(meeting_start_charles),
                    "end_time": minutes_to_time(meeting_end_charles)
                }
            ],
            "friends_met": 1,
            "finish_time": meeting_end_charles,
            "total_travel_time": travel_to_charles
        }
        candidates.append(candidate_charles)

    # Candidate 3: Attempt to meet both, Option A: Bayview -> Union Square -> Presidio.
    # Start with Richard at Union Square then go to Charles at Presidio.
    travel_to_richard = travel_times[("Bayview", richard_location)]
    arrival_richard = bayview_arrival + travel_to_richard
    meeting_start_richard = max(arrival_richard, richard_avail_start)
    # Assign full minimum meeting for Richard first.
    meeting_end_richard = meeting_start_richard + richard_min
    travel_richard_to_charles = travel_times[("Union Square", charles_location)]
    arrival_charles_via_richard = meeting_end_richard + travel_richard_to_charles
    meeting_start_charles_via_richard = max(arrival_charles_via_richard, charles_avail_start)
    meeting_end_charles_via_richard = meeting_start_charles_via_richard + charles_min
    if meeting_end_charles_via_richard <= charles_avail_end:
        candidate_both_A = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": richard_location,
                    "person": "Richard",
                    "start_time": minutes_to_time(meeting_start_richard),
                    "end_time": minutes_to_time(meeting_end_richard)
                },
                {
                    "action": "meet",
                    "location": charles_location,
                    "person": "Charles",
                    "start_time": minutes_to_time(meeting_start_charles_via_richard),
                    "end_time": minutes_to_time(meeting_end_charles_via_richard)
                }
            ],
            "friends_met": 2,
            "finish_time": meeting_end_charles_via_richard,
            "total_travel_time": travel_to_richard + travel_richard_to_charles
        }
        candidates.append(candidate_both_A)

    # Candidate 4: Attempt to meet both, Option B: Bayview -> Presidio -> Union Square.
    travel_to_charles = travel_times[("Bayview", charles_location)]
    arrival_charles = bayview_arrival + travel_to_charles
    meeting_start_charles = max(arrival_charles, charles_avail_start)
    meeting_end_charles = meeting_start_charles + charles_min
    travel_charles_to_richard = travel_times[(charles_location, richard_location)]
    arrival_richard_via_charles = meeting_end_charles + travel_charles_to_richard
    meeting_start_richard_via_charles = max(arrival_richard_via_charles, richard_avail_start)
    meeting_end_richard_via_charles = meeting_start_richard_via_charles + richard_min
    if meeting_end_richard_via_charles <= richard_avail_end:
        candidate_both_B = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": charles_location,
                    "person": "Charles",
                    "start_time": minutes_to_time(meeting_start_charles),
                    "end_time": minutes_to_time(meeting_end_charles)
                },
                {
                    "action": "meet",
                    "location": richard_location,
                    "person": "Richard",
                    "start_time": minutes_to_time(meeting_start_richard_via_charles),
                    "end_time": minutes_to_time(meeting_end_richard_via_charles)
                }
            ],
            "friends_met": 2,
            "finish_time": meeting_end_richard_via_charles,
            "total_travel_time": travel_to_charles + travel_charles_to_richard
        }
        candidates.append(candidate_both_B)

    # Choose the optimal candidate:
    # Our primary objective is to maximize the number of friends met.
    # In case of tie, we choose the schedule with the earliest finish time and then lower total travel time.
    if candidates:
        candidates.sort(key=lambda x: (-x["friends_met"], x["finish_time"], x["total_travel_time"]))
        best_itinerary = candidates[0]["itinerary"]
    else:
        best_itinerary = []

    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()