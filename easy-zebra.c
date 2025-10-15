#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#ifndef __CPROVER
void __CPROVER_assume(bool condition);
void __CPROVER_assert(bool condition, const char *message);
#endif

#define __CPROVER_unique_domain(field, field_domain_array)                                  {                                                                                               size_t index;                                                                               __CPROVER_assume(index < (sizeof(field_domain_array) / sizeof(field_domain_array[0])));     __CPROVER_assume(!field_domain_array##_used[index]);                                        field_domain_array##_used[index] = true;                                                    field = field_domain_array[index];                                                      }

size_t __CPROVER_nondet_array_index(size_t length) {
    size_t index;
    __CPROVER_assume(index < length);
    return index;
}

#define __CPROVER_nondet_index(array)                                  __CPROVER_nondet_array_index(sizeof(array) / sizeof(array[0]))

#define __CPROVER_nondet_element(array)        (array)[__CPROVER_nondet_index(array)]

static size_t __CPROVER_index_tmp;

static size_t __CPROVER_index_dispatch(bool comparison) {
    __CPROVER_assume(comparison);
    return __CPROVER_index_tmp;
}

#define __CPROVER_index(array, value)     __CPROVER_index_dispatch(array[__CPROVER_index_tmp = __CPROVER_nondet_index(array)] == value)

typedef enum { GREEN, PINK, PURPLE, YELLOW } Laptop;
typedef enum { EMILY, KIMBERLY, LAUREN, SAMANTHA } Name;
typedef enum { LAVADOME, SCORIACONE, SUBMARINE, SUPERVOLCANO } Volcano;
typedef enum { FLUCTUATING, INCREASING, STABLE, VERYHIGH } Activity;

struct Volcanologist {
    int id;
    Laptop laptop;
    Name name;
    Volcano volcano;
    Activity activity;
};

static int Volcanologist_id[] = {1, 2, 3, 4};
static bool Volcanologist_id_used[4];

static Laptop Volcanologist_laptop[] = { GREEN, PINK, PURPLE, YELLOW };
static bool Volcanologist_laptop_used[4];

static Name Volcanologist_name[] = { EMILY, KIMBERLY, LAUREN, SAMANTHA };
static bool Volcanologist_name_used[4];

static Volcano Volcanologist_volcano[] = { LAVADOME, SCORIACONE, SUBMARINE, SUPERVOLCANO };
static bool Volcanologist_volcano_used[4];

static Activity Volcanologist_activity[] = { FLUCTUATING, INCREASING, STABLE, VERYHIGH };
static bool Volcanologist_activity_used[4];

static void init_Volcanologist(struct Volcanologist * instance) {
    __CPROVER_unique_domain(instance->id, Volcanologist_id);
    __CPROVER_unique_domain(instance->laptop, Volcanologist_laptop);
    __CPROVER_unique_domain(instance->name, Volcanologist_name);
    __CPROVER_unique_domain(instance->volcano, Volcanologist_volcano);
    __CPROVER_unique_domain(instance->activity, Volcanologist_activity);
}

struct Solution {
    struct Volcanologist volcanologists[4];
};

static void init_Solution(struct Solution * instance) {
    for (size_t i = 0; i < sizeof(instance->volcanologists) / sizeof(instance->volcanologists[0]); ++i) {
        init_Volcanologist(&instance->volcanologists[i]);
    }
}

static void validate(struct Solution solution) {
    typeof(__CPROVER_nondet_element(solution.volcanologists)) very_high_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(very_high_volcanologist.id == 2);
    __CPROVER_assume(very_high_volcanologist.activity == VERYHIGH);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) supervolcano_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(supervolcano_volcanologist.id == 3);
    __CPROVER_assume(supervolcano_volcanologist.volcano == SUPERVOLCANO);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) lavadome_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(lavadome_volcanologist.volcano == LAVADOME);
    __CPROVER_assume(lavadome_volcanologist.id == supervolcano_volcanologist.id + 1);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) scoriacone_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(scoriacone_volcanologist.volcano == SCORIACONE);
    __CPROVER_assume(scoriacone_volcanologist.activity == FLUCTUATING);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) lauren_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(lauren_volcanologist.name == LAUREN);
    __CPROVER_assume(lauren_volcanologist.id == 2);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) stable_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(stable_volcanologist.activity == STABLE);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) samantha_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(samantha_volcanologist.name == SAMANTHA);
    __CPROVER_assume(__CPROVER_abs(stable_volcanologist.id - samantha_volcanologist.id) == 1);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) submarine_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(submarine_volcanologist.volcano == SUBMARINE);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) yellow_laptop_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(yellow_laptop_volcanologist.laptop == YELLOW);
    __CPROVER_assume(submarine_volcanologist.id == yellow_laptop_volcanologist.id + 1);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) increasing_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(increasing_volcanologist.activity == INCREASING);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) pink_laptop_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(pink_laptop_volcanologist.laptop == PINK);
    __CPROVER_assume(increasing_volcanologist.id == pink_laptop_volcanologist.id + 1);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) emily_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(emily_volcanologist.name == EMILY);
    typeof(__CPROVER_nondet_element(solution.volcanologists)) purple_laptop_volcanologist = __CPROVER_nondet_element(solution.volcanologists);
    __CPROVER_assume(purple_laptop_volcanologist.laptop == PURPLE);
    __CPROVER_assume(emily_volcanologist.id == purple_laptop_volcanologist.id + 1);
    __CPROVER_assume(lauren_volcanologist.id == emily_volcanologist.id - 1);
}

#ifndef __CPROVER
void __CPROVER_output(const char *name, struct Solution solution);
#endif

int main(void) {
    struct Solution solution;
    init_Solution(&solution);
    validate(solution);

    __CPROVER_output("solution", solution);
    __CPROVER_assert(false, "");
}