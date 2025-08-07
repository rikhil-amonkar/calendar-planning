from z3 import *
import json

def main():
    # Convert all times to minutes from midnight
    start_sunset = 9 * 60  # 9:00 AM

    # Availability times in minutes
    michelle_end_time = 14 * 60  # 2:00 PM
    robert_end_time = 13 * 60 + 45  # 1:45 PM
    george_start_time = 10 * 60 + 30  # 10:30 AM
    george_end_time = 18 * 60 + 45  # 6:45 PM
    william_start_time = 18 * 60 + 30  # 6:30 PM
    william_end_time = 20 * 60 + 45  # 8:45 PM

    # Travel times from Sunset District to each location
    travel_sunset = {
        'Michelle': 30,  # Sunset to Chinatown
        'Robert': 29,    # Sunset to Fisherman's Wharf
        'George': 16     # Sunset to Presidio
    }

    # Travel times between locations
    travel_between = {
        ('Michelle', 'Robert'): 8,   # Chinatown to Fisherman's Wharf
        ('Michelle', 'George'): 19,  # Chinatown to Presidio
        ('Robert', 'Michelle'): 12,  # Fisherman's Wharf to Chinatown
        ('Robert', 'George'): 17,    # Fisherman's Wharf to Presidio
        ('George', 'Michelle'): 21,  # Presidio to Chinatown
        ('George', 'Robert'): 19     # Presidio to Fisherman's Wharf
    }

    # Travel times from each location to Russian Hill (William)
    travel_to_rh = {
        'Michelle': 7,  # Chinatown to Russian Hill
        'Robert': 7,    # Fisherman's Wharf to Russian Hill
        'George': 14    # Presidio to Russian Hill
    }

    # Meeting durations in minutes
    durations = {
        'Michelle': 15,
        'Robert': 30,
        'George': 30,
        'William': 105
    }

    # Create Z3 variables for start times
    start_m = Real('start_m')  # Michelle
    start_r = Real('start_r')  # Robert
    start_g = Real('start_g')  # George
    start_w = Real('start_w')  # William

    # Create order variables (0,1,2 for first three meetings)
    order0 = Int('order0')
    order1 = Int('order1')
    order2 = Int('order2')

    s = Solver()

    # Define the order: each must be 0,1,2 and distinct
    s.add(order0 >= 0, order0 <= 2)
    s.add(order1 >= 0, order1 <= 2)
    s.add(order2 >= 0, order2 <= 2)
    s.add(Distinct(order0, order1, order2))

    # Map order indices to friends
    friends = ['Michelle', 'Robert', 'George']

    # Start time constraints for the first meeting
    first_meeting = If(order0 == 0, start_m, If(order0 == 1, start_r, start_g))
    s.add(first_meeting == start_sunset + travel_sunset[friends[order0]])

    # End times for each meeting
    end_m = start_m + durations['Michelle']
    end_r = start_r + durations['Robert']
    end_g = start_g + durations['George']

    # End time of the first meeting
    end0 = If(order0 == 0, end_m, If(order0 == 1, end_r, end_g))

    # Start time of the second meeting
    second_meeting = If(order1 == 0, start_m, If(order1 == 1, start_r, start_g))
    # Travel time from first to second location
    from_friend = friends[order0]
    to_friend = friends[order1]
    travel_time = travel_between[(from_friend, to_friend)]
    s.add(second_meeting >= end0 + travel_time)

    # End time of the second meeting
    end1 = If(order1 == 0, end_m, If(order1 == 1, end_r, end_g))

    # Start time of the third meeting
    third_meeting = If(order2 == 0, start_m, If(order2 == 1, start_r, start_g))
    # Travel time from second to third location
    from_friend = friends[order1]
    to_friend = friends[order2]
    travel_time = travel_between[(from_friend, to_friend)]
    s.add(third_meeting >= end1 + travel_time)

    # End time of the third meeting
    end2 = If(order2 == 0, end_m, If(order2 == 1, end_r, end_g))

    # Start time for William: after travel from the last meeting location
    last_friend = friends[order2]
    travel_time_to_rh = travel_to_rh[last_friend]
    s.add(start_w >= end2 + travel_time_to_rh)
    s.add(start_w >= william_start_time)
    end_w = start_w + durations['William']
    s.add(end_w <= william_end_time)

    # Availability constraints for Michelle, Robert, and George
    s.add(start_m >= 8*60+15)  # Michelle available from 8:15 AM
    s.add(end_m <= michelle_end_time)
    s.add(start_r >= 9*60)     # Robert available from 9:00 AM
    s.add(end_r <= robert_end_time)
    s.add(start_g >= george_start_time)
    s.add(end_g <= george_end_time)

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Convert model values to integers
        def get_time(var):
            val = m[var]
            if is_algebraic_value(val):
                return val.approx(10).as_long()
            else:
                return val.as_long()

        start_m_val = get_time(start_m)
        end_m_val = start_m_val + durations['Michelle']
        start_r_val = get_time(start_r)
        end_r_val = start_r_val + durations['Robert']
        start_g_val = get_time(start_g)
        end_g_val = start_g_val + durations['George']
        start_w_val = get_time(start_w)
        end_w_val = start_w_val + durations['William']

        # Determine order of first three meetings
        order0_val = m[order0].as_long()
        order1_val = m[order1].as_long()
        order2_val = m[order2].as_long()

        # Map order to meeting details
        meetings = []
        first_friend = friends[order0_val]
        meetings.append((first_friend, start_m_val if first_friend == 'Michelle' else start_r_val if first_friend == 'Robert' else start_g_val, 
                         end_m_val if first_friend == 'Michelle' else end_r_val if first_friend == 'Robert' else end_g_val))

        second_friend = friends[order1_val]
        meetings.append((second_friend, start_m_val if second_friend == 'Michelle' else start_r_val if second_friend == 'Robert' else start_g_val, 
                         end_m_val if second_friend == 'Michelle' else end_r_val if second_friend == 'Robert' else end_g_val))

        third_friend = friends[order2_val]
        meetings.append((third_friend, start_m_val if third_friend == 'Michelle' else start_r_val if third_friend == 'Robert' else start_g_val, 
                         end_m_val if third_friend == 'Michelle' else end_r_val if third_friend == 'Robert' else end_g_val))

        meetings.append(('William', start_w_val, end_w_val))

        # Sort meetings by start time
        meetings.sort(key=lambda x: x[1])

        # Convert times to HH:MM format
        def to_hhmm(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        itinerary = []
        for person, start, end in meetings:
            itinerary.append({
                "action": "meet",
                "person": person,
                "start_time": to_hhmm(start),
                "end_time": to_hhmm(end)
            })

        # Output as JSON
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()