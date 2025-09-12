# Define necessary data structures
friend_idx = [0, 1, 2]  # Example friend indices for each meeting
start_time = [60, 120, 180]  # Start times in minutes
end_time = [90, 150, 210]  # End times in minutes

friends = [
    {"name": "Alice", "location": 0},
    {"name": "Bob", "location": 1},
    {"name": "Charlie", "location": 2}
]

locations_names = ["Home", "Park", "Cafe"]
itinerary = []

# Loop over each meeting index
for i in range(len(friend_idx)):
    fid = friend_idx[i]
    if fid != 9:
        j = fid
        st = start_time[i]
        et = end_time[i]
        loc_idx = friends[j]["location"]
        loc_name = locations_names[loc_idx]
        name = friends[j]["name"]

        def to_time_str(m):
            h = m // 60
            mm = m % 60
            return f"{h}:{mm:02d}"

        start_str = to_time_str(st)
        end_str = to_time_str(et)

        itinerary.append({
            "action": "meet",
            "location": loc_name,
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })

# Output the itinerary for verification
print(itinerary)