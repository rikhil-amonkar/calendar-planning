#!/usr/bin/env python3
import json

def format_time(minutes):
    # Convert minutes after midnight into "H:MM" (24-hour format with no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define times in minutes after midnight
    # 9:00 = 540, 12:00 = 720, 15:30 = 930, 15:45 = 945, 19:15 = 1155
    start_nob_hill = 9 * 60          # 9:00 -> 540
    kenneth_avail_start = 12 * 60      # 12:00 -> 720
    kenneth_avail_end = 15 * 60 + 45   # 15:45 -> 945
    thomas_avail_start = 15 * 60 + 30  # 15:30 -> 930
    thomas_avail_end = 19 * 60 + 15    # 19:15 -> 1155

    # Minimum meeting durations (in minutes)
    min_duration_kenneth = 45
    min_duration_thomas = 75

    # Travel times (in minutes)
    travel_nobhill_to_mission = 13
    travel_mission_to_pacific = 16
    # (Other travel times are provided but for this itinerary we follow:
    # Nob Hill -> Mission District -> Pacific Heights)

    # We want to schedule a meeting with Kenneth (at Mission District) and then Thomas (at Pacific Heights).
    #
    # Our decision variable:
    #   T = start time (in minutes after midnight) for meeting Kenneth.
    # Constraints for Kenneth:
    #   T must be at least kenneth_avail_start (720) and
    #   meeting end T + min_duration_kenneth must be <= kenneth_avail_end (945).
    #
    # Also, we must depart from Nob Hill to Mission District so that we arrive by T.
    #   Departure time from Nob Hill = T - travel_nobhill_to_mission, and must be >= start_nob_hill.
    #
    # After the meeting with Kenneth, travel to Pacific Heights takes travel_mission_to_pacific minutes.
    # Let arrival_at_pacific = T + min_duration_kenneth + travel_mission_to_pacific.
    #
    # Thomas is available starting at thomas_avail_start (930). So his meeting will start at:
    #   meeting_start_thomas = max(thomas_avail_start, arrival_at_pacific)
    # and will last min_duration_thomas minutes.
    # Also, we need meeting_start_thomas + min_duration_thomas <= thomas_avail_end.
    #
    # For this problem, many candidate T values are feasible.
    # In our search we choose the candidate that minimizes the maximum waiting period in our schedule.
    # Waiting occurs (a) at Nob Hill before leaving and (b) at Pacific Heights waiting for Thomas.
    
    best_candidate = None
    best_max_wait = None

    # If we start Kenneth as early as possible, we depart Nob Hill at (T - travel_nobhill_to_mission)
    # and if we finish early, we might wait at Pacific Heights for Thomas.
    #
    # We'll search candidate T in whole minutes from kenneth_avail_start up to the latest possible start time.
    # The latest T must satisfy:
    #   T + min_duration_kenneth <= kenneth_avail_end  --> T <= kenneth_avail_end - min_duration_kenneth (i.e. 945-45 = 900)
    # Also, if T + min_duration_kenneth + travel_mission_to_pacific <= thomas_avail_start then Thomas meeting
    # starts at thomas_avail_start, ensuring the overall schedule finishes at thomas_avail_start + min_duration_thomas.
    # In that case T must be such that T <= thomas_avail_start - (min_duration_kenneth + travel_mission_to_pacific)
    #   i.e. T <= 930 - (45 + 16) = 930 - 61 = 869.
    # For T values above 869, Thomas meeting would be delayed beyond 15:30.
    #
    # We will consider T in the range [kenneth_avail_start, min(900, 869)].
    
    feasible_T_end = min(900, 869)
    
    for T in range(kenneth_avail_start, feasible_T_end + 1):
        departure_nobhill = T - travel_nobhill_to_mission
        if departure_nobhill < start_nob_hill:
            continue  # Not feasible because we haven't arrived at Nob Hill yet
        
        # Waiting at Nob Hill: time from arrival (9:00) to departure from Nob Hill
        wait_nobhill = departure_nobhill - start_nob_hill
        
        # Kenneth meeting from T to T + min_duration_kenneth
        meeting_kenneth_end = T + min_duration_kenneth
        
        # Travel from Mission District to Pacific Heights
        arrival_pacific = meeting_kenneth_end + travel_mission_to_pacific
        
        # Waiting at Pacific Heights until Thomas is available:
        wait_pacific = max(0, thomas_avail_start - arrival_pacific)
        
        # Maximum waiting segment
        max_wait = max(wait_nobhill, wait_pacific)
        
        # Determine Thomas meeting start and finish
        meeting_thomas_start = thomas_avail_start if arrival_pacific <= thomas_avail_start else arrival_pacific
        meeting_thomas_end = meeting_thomas_start + min_duration_thomas
        
        # Check that Thomas meeting fits in his available window
        if meeting_thomas_end > thomas_avail_end:
            continue

        # For this problem, the total idle wait (wait_nobhill + wait_pacific) is constant,
        # but we choose the candidate that minimizes the maximum single waiting period.
        if best_candidate is None or max_wait < best_max_wait:
            best_candidate = T
            best_max_wait = max_wait

    if best_candidate is None:
        # No valid schedule found.
        schedule = {"itinerary": []}
    else:
        T = best_candidate
        # Calculate the computed times
        departure_nobhill = T - travel_nobhill_to_mission
        meeting_kenneth_start = T
        meeting_kenneth_end = T + min_duration_kenneth
        arrival_pacific = meeting_kenneth_end + travel_mission_to_pacific
        meeting_thomas_start = thomas_avail_start if arrival_pacific <= thomas_avail_start else arrival_pacific
        meeting_thomas_end = meeting_thomas_start + min_duration_thomas

        schedule = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": "Mission District",
                    "person": "Kenneth",
                    "start_time": format_time(meeting_kenneth_start),
                    "end_time": format_time(meeting_kenneth_end)
                },
                {
                    "action": "meet",
                    "location": "Pacific Heights",
                    "person": "Thomas",
                    "start_time": format_time(meeting_thomas_start),
                    "end_time": format_time(meeting_thomas_end)
                }
            ]
        }

    print(json.dumps(schedule))

if __name__ == "__main__":
    main()