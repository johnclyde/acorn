<script lang="ts">
  export let clause: ClauseInfo;
  export let onClick: null | ((id: number) => void) = null;
</script>

{#if clause.id !== null}
  <span
    class="indent clause-link"
    on:click={() => {
      if (clause.id !== null && onClick !== null) {
        onClick(clause.id);
      }
    }}>{clause.text}</span
  >
{:else}
  <span class="indent">{clause.text}</span>
{/if}

<style>
  .clause-link {
    cursor: pointer;
  }

  .clause-link:hover {
    text-decoration: underline;
  }
</style>
