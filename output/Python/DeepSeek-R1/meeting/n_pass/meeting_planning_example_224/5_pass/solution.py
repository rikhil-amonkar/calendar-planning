import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Fisherman\'s Wharf': {
            'Golden Gate Park': 25,
            'Presidio': 17,
            'Richmond District': 18
        },
        'Golden Gate Park': {
            'Fisherman\'s Wharf': 25,
            'Presidio': 11,
            'Richmond District': 9
        },
        'Presidio': {
            'Fisherman\'s Wharf': 17,
            'Golden Gate Park': 11,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    start_fw = 9 * 60  # 9:00 AM

    # Travel from Fisherman's Wharf to Golden Gate Park
    travel1_start = start_fw
    travel1_end = start_fw + travel_times['Fisherman\'s Wharf']['Golden Gate Park']  # 9:25

    # Meet Melissa until we need to leave for Richmond District to meet Emily at 6:00 PM
    travel_to_rd = travel_times['Golden Gate Park']['Richmond District']  # 9 minutes
    # Arrive at Richmond District by 18:00 (6:00 PM)
    arrive_rd_time = 18 * 60  # 18:00 in minutes
    leave_ggp_time = arrive_rd_time - travel_to_rd  # 17:51
    melissa_start = travel1_end  # 9:25
    melissa_end = leave_ggp_time  # 17:51

    # Travel from Golden Gate Park to Richmond District
    travel2_start = melissa_end  # 17:51
    travel2_end = travel2_start + travel_to_rd  # 18:00

    # Meet Emily for exactly 2 hours
    emily_start = travel2_end  # 18:00
    emily_end = emily_start + 120  # 20:00

    # Travel from Richmond District to Presidio
    travel3_start = emily_end  # 20:00
    travel3_end = travel3_start + travel_times['Richmond District']['Presidio']  # 20:07

    # Meet Nancy for at least 105 minutes
    nancy_start = travel3_end  # 20:07
    nancy_end = nancy_start + 105  # 21:52

    itinerary = [
        {
            "action": "travel",
            "from": "Fisherman's Wharf",
            "to": "Golden Gate Park",
            "start_time": format_time(travel1_start),
            "end_time": format_time(travel1_end)
        },
        {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Melissa",
            "start_time": format_time(melissa_start),
            "end_time": format_time(melissa_end)
        },
        {
            "action": "travel",
            "from": "Golden Gate Park",
            "to": "Richmond District",
            "start_time": format_time(travel2_start),
            "end_time": format_time(travel2_end)
        },
        {
            "action": "meet",
            "location": "Richmond District",
            "person": "Emily",
            "start_time": format_time(emily_start),
            "end_time": format_time(emily_end)
        },
        {
            "action": "travel",
            "from": "Richmond District",
            "to": "Presidio",
            "start_time": format_time(travel3_start),
            "end_time": format_time(travel3_end)
        },
        {
            "action": "meet",
            "location": "Presidio",
            "person": "Nancy",
            "start_time": format_time(nancy_start),
            "end_time": format_time(nancy_end)
        }
    ]

    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()