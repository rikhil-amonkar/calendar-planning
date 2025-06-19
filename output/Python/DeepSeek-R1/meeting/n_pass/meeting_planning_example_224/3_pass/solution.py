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
            'Fisherman\'s Wharf': 24,
            'Presidio': 11,
            'Richmond District': 7
        },
        'Presidio': {
            'Fisherman\'s Wharf': 19,
            'Golden Gate Park': 12,
            'Richmond District': 7
        },
        'Richmond District': {
            'Fisherman\'s Wharf': 18,
            'Golden Gate Park': 9,
            'Presidio': 7
        }
    }

    start_fw = 9 * 60  # 9:00 AM

    t_fw_to_ggp = travel_times['Fisherman\'s Wharf']['Golden Gate Park']
    t_ggp_to_rd = travel_times['Golden Gate Park']['Richmond District']
    t_rd_to_presidio = travel_times['Richmond District']['Presidio']

    min_duration_emily = 120
    min_duration_nancy = 105

    nancy_available_start = 19 * 60 + 45  # 7:45 PM

    # Start: Fisherman's Wharf at 9:00 AM
    travel1_start = start_fw
    travel1_end = start_fw + t_fw_to_ggp  # 9:25 AM

    # Meet Melissa: start immediately after arrival (9:25 AM)
    melissa_start = travel1_end

    # Calculate the latest time we can leave Golden Gate Park to meet all constraints
    # We must leave Richmond District by: nancy_available_start - travel time to Presidio
    leave_richmond_by = nancy_available_start - t_rd_to_presidio  # 19:38
    # Emily meeting duration is 2 hours, so Emily meeting must start by:
    emily_start_by = leave_richmond_by - min_duration_emily  # 17:38
    # Therefore, we must leave Golden Gate Park by:
    leave_ggp_by = emily_start_by - t_ggp_to_rd  # 17:31

    melissa_end = leave_ggp_by  # 17:31

    # Travel from Golden Gate Park to Richmond District
    travel2_start = melissa_end  # 17:31
    travel2_end = travel2_start + t_ggp_to_rd  # 17:38

    # Meet Emily: start immediately after arrival (17:38) for 2 hours
    emily_start = travel2_end
    emily_end = emily_start + min_duration_emily  # 19:38

    # Travel from Richmond District to Presidio
    travel3_start = emily_end  # 19:38
    travel3_end = travel3_start + t_rd_to_presidio  # 19:45

    # Meet Nancy: start immediately after arrival (19:45) for 105 minutes
    nancy_start = travel3_end
    nancy_end = nancy_start + min_duration_nancy  # 21:30

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