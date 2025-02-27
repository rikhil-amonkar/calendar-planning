def find_earliest_available_time(start_time, end_time, busy_slots):
    """
    Find the earliest available time slot that is at least 30 minutes long.

    Args:
        start_time (int): The start time of the work hours in minutes.
        end_time (int): The end time of the work hours in minutes.
        busy_slots (list): A list of busy time slots in minutes.

    Returns:
        tuple or None: The earliest available time slot in minutes (start, end) or None if no available time slot is found.
    """
    # Convert busy slots to minutes
    busy_slots = [slot for slot in busy_slots if start_time <= slot[0] <= end_time]
    busy_slots = [(slot[0], slot[1]) for slot in busy_slots]

    # Sort busy slots in ascending order
    busy_slots.sort(key=lambda x: x[0])

    # Initialize the earliest available time slot
    earliest_available_slot = None

    # Iterate over the busy slots to find the earliest available time slot
    for i in range(len(busy_slots)):
        # If this is the first busy slot or the current busy slot does not overlap with the previous one
        if i == 0 or busy_slots[i][0] > busy_slots[i-1][1]:
            # Check if there is an available time slot of at least 30 minutes
            if busy_slots[i][0] - start_time >= 30 or end_time - busy_slots[i][1] >= 30:
                # Update the earliest available time slot
                if earliest_available_slot is None or busy_slots[i][0] - start_time < earliest_available_slot[0] - start_time:
                    earliest_available_slot = (max(start_time, busy_slots[i-1][1] if i > 0 else start_time), min(end_time, busy_slots[i][0] if i < len(busy_slots) - 1 else end_time))
        # If the current busy slot overlaps with the previous one, merge them
        elif busy_slots[i][0] < busy_slots[i-1][1]:
            busy_slots[i] = (busy_slots[i-1][0], max(busy_slots[i-1][1], busy_slots[i][1]))

    return earliest_available_slot


def main():
    # Define the work hours and busy slots
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60  # 17:00
    busy_slots = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60, 16 * 60 + 30)]

    # Find the earliest available time slot
    earliest_available_slot = find_earliest_available_time(start_time, end_time, busy_slots)

    # Print the result
    if earliest_available_slot:
        print(f"The proposed time is: Monday, {earliest_available_slot[0] // 60:02d}:{earliest_available_slot[0] % 60:02d} - {earliest_available_slot[1] // 60:02d}:{earliest_available_slot[1] % 60:02d}")
    else:
        print("No available time slot is found.")


if __name__ == "__main__":
    main()
    