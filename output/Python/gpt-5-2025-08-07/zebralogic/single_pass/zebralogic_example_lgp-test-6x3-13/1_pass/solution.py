import json
import itertools

def solve():
    houses = [1, 2, 3, 4, 5, 6]  # left to right
    Names = ["Bob", "Arnold", "Carol", "Alice", "Peter", "Eric"]
    BookGenres = ["romance", "historical fiction", "biography", "mystery", "fantasy", "science fiction"]
    Occupations = ["artist", "doctor", "nurse", "engineer", "teacher", "lawyer"]

    # Helpers
    def idx_of(value, seq):
        return seq.index(value)

    def adjacent(i, j):
        return abs(i - j) == 1

    solutions = []

    # Pre-placed/fixed facts:
    # - Eric is in the third house (index 2)
    # - Doctor is in the first house (index 0)
    # - Carol loves mystery (maps name->genre)
    # - Alice loves fantasy and is a lawyer (maps name->genre and name->job)
    # - Mystery not in 5th house (index 4): since Carol is mystery, Carol not at index 4
    # - Bob not in 5th house (index 4)
    # - Nurse directly left of Alice: implies Alice not in house 1 or 2
    # Names constraints: create permutations with Eric fixed at index 2.
    others = [n for n in Names if n != "Eric"]
    for perm in itertools.permutations(others):
        names = list(perm[:2]) + ["Eric"] + list(perm[2:])  # insert Eric at index 2

        # Quick name-based pruning
        alice_i = idx_of("Alice", names)
        bob_i = idx_of("Bob", names)
        carol_i = idx_of("Carol", names)

        # Alice cannot be in houses 1 or 2 (nurse must be directly left), and not 3 (occupied by Eric)
        if alice_i in (0, 1, 2):
            continue

        # Bob not in 5th house (index 4)
        if bob_i == 4:
            continue

        # Carol (mystery) not in 5th house
        if carol_i == 4:
            continue

        # Bob adjacent to Carol (mystery person)
        if not adjacent(bob_i, carol_i):
            continue

        # Now assign occupations with constraints:
        # jobs[0] = doctor
        # jobs[alice_i] = lawyer
        # jobs[alice_i - 1] = nurse
        # Arnold is to the left of the engineer
        jobs = [None] * 6
        jobs[0] = "doctor"
        # If Alice at index <=0 or ==1 would break nurse placement, already filtered
        jobs[alice_i] = "lawyer"
        jobs[alice_i - 1] = "nurse"

        fixed_positions = {0, alice_i, alice_i - 1}
        remaining_positions = [i for i in range(6) if i not in fixed_positions]
        remaining_jobs = ["artist", "engineer", "teacher"]

        valid_job_assignments = []
        for job_perm in itertools.permutations(remaining_jobs):
            trial_jobs = jobs[:]
            for pos, job in zip(remaining_positions, job_perm):
                trial_jobs[pos] = job

            # Arnold left of engineer
            arnold_i = idx_of("Arnold", names)
            engineer_i = idx_of("engineer", trial_jobs)
            if not (arnold_i < engineer_i):
                continue

            valid_job_assignments.append(trial_jobs)

        if not valid_job_assignments:
            continue

        # For each valid job assignment, assign books with constraints
        for jobs_assigned in valid_job_assignments:
            books = [None] * 6

            # Alice loves fantasy
            books[alice_i] = "fantasy"
            # Carol loves mystery
            books[carol_i] = "mystery"
            # Teacher <-> biography
            teacher_i = idx_of("teacher", jobs_assigned)
            books[teacher_i] = "biography"
            # Artist <-> science fiction
            artist_i = idx_of("artist", jobs_assigned)
            books[artist_i] = "science fiction"

            # Mystery not in 5th house
            if books[4] == "mystery":
                continue

            # Fill remaining two genres: romance and historical fiction
            remaining_genres = set(BookGenres) - set(books)
            # Should be exactly two left
            if remaining_genres != {"romance", "historical fiction"}:
                continue

            empty_positions = [i for i, b in enumerate(books) if b is None]
            # Try both assignments of the two remaining genres
            for perm_genres in itertools.permutations(list(remaining_genres)):
                trial_books = books[:]
                for pos, g in zip(empty_positions, perm_genres):
                    trial_books[pos] = g

                # Historical fiction is somewhere to the left of the teacher
                hist_i = idx_of("historical fiction", trial_books)
                if not (hist_i < teacher_i):
                    continue

                # All constraints satisfied; record solution
                solutions.append((names[:], trial_books[:], jobs_assigned[:]))

    # Expect a unique solution; if multiple, take the first
    if not solutions:
        raise RuntimeError("No solution found.")
    names_sol, books_sol, jobs_sol = solutions[0]

    # Prepare JSON output
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": []
        }
    }
    for i in range(6):
        result["solution"]["rows"].append(
            [str(houses[i]), names_sol[i], books_sol[i], jobs_sol[i]]
        )

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve()