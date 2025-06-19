# Define the schedule dictionary
schedule = {
    "Nicole": ["08:00-09:00", "10:00-11:00", "14:00-15:00"],
    "John": ["09:00-10:00", "11:00-12:00", "15:00-16:00"]
}

# Define the time to check
time = "09:00-10:00"

# Define the function to check if time is in a schedule
def check_time_in_schedule(schedule, time):
    for person, slots in schedule.items():
        if time in slots:
            return f"The time '{time}' is in {person}'s schedule."
    return f"The time '{time}' is not in any schedule."

# Check if time is in Nicole's schedule
if all(time not in slot for slot in schedule['Nicole']):
    # Add an indented block here to handle the condition
    print("The time is not in any slot of Nicole's schedule.")
else:
    print("The time is in one or more slots of Nicole's schedule.")

# Check if time is in any schedule
print(check_time_in_schedule(schedule, time))